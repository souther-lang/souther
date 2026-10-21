package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container asked for what two different fields of its elements come to: one element holds a
 * figure at both fields, so the elements are chosen for both totals together and a row has to
 * meet each of them.
 */
class SeveralTotalsOfDifferentFieldsOfOneContainerAreComposedTogetherTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final Pattern POSTING =
            Pattern.compile("Posting \\{ amount = (-?\\d+), fee = (-?\\d+) }");

    private static final String MODULE = """
            module example.ledger

            data Posting = { amount: Int, fee: Int }
            %s
            behavior both : (ps: List<Posting>) -> Bool

            let both (ps) =
                %s
            """;

    private static final String AMOUNT = "List.sum(List.map(p -> p.amount, ps)) >= 100";

    private static final String FEE = "List.sum(List.map(p -> p.fee, ps)) >= 5";

    /** What the postings of an offered row come to at each field, and how many there are. */
    private record Sums(int amount, int fee, int count, boolean feeWithinAmount) {

        static Sums of(String row) {
            Matcher postings = POSTING.matcher(row);
            int amount = 0;
            int fee = 0;
            int count = 0;
            boolean within = true;
            while (postings.find()) {
                int each = Integer.parseInt(postings.group(1));
                int charged = Integer.parseInt(postings.group(2));
                amount += each;
                fee += charged;
                count++;
                within &= charged <= each;
            }
            return new Sums(amount, fee, count, within);
        }

        boolean meetsBoth() {
            return amount >= 100 && fee >= 5;
        }
    }

    @Test
    void rowsAreOfferedAtTheEdgesOfBothTotals() {
        Compilation compilation = measuredWithItsOwnRows(
                MODULE.formatted("", AMOUNT + "\n            && " + FEE), Sums::meetsBoth);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
        assertFalse(report(compilation).contains("no row takes a decision rule"),
                () -> report(compilation));
    }

    @Test
    void theOrderTheTotalsAreWrittenInDoesNotChooseWhichOfThemIsComposed() {
        Compilation compilation = measuredWithItsOwnRows(
                MODULE.formatted("", FEE + "\n            && " + AMOUNT), Sums::meetsBoth);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
    }

    @Test
    void aSizeAskedBesideTheTotalsIsTheSizeOfTheOneContainerTheyAreComposedFor() {
        Compilation compilation = measuredWithItsOwnRows(
                MODULE.formatted("", "List.length(ps) == 2\n            && " + AMOUNT
                        + "\n            && " + FEE),
                sums -> sums.meetsBoth() && sums.count() == 2);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
        assertTrue(offeredInputs(compilation, "both").stream().map(Sums::of)
                        .allMatch(sums -> sums.count() == 2),
                () -> "every offered row holds the size asked for: " + report(compilation));
    }

    @Test
    void whatTheElementsTypeRequiresOfAFeeBesideItsAmountIsKeptByEveryElement() {
        String source = MODULE.formatted("    invariant fee <= amount\n",
                AMOUNT + "\n            && " + FEE);
        Compilation compilation = measured(source);
        List<String> rows = offeredInputs(compilation, "both");
        assertFalse(rows.isEmpty(), () -> "rows are offered: " + report(compilation));
        assertTrue(rows.stream().map(Sums::of).allMatch(Sums::feeWithinAmount),
                () -> "every element of an offered row keeps the rule: " + rows);
        assertTrue(rows.stream().map(Sums::of).anyMatch(Sums::meetsBoth),
                () -> "a row meets both totals: " + rows);
    }

    /**
     * The second total reads the field the first does, so the shares of the two are not figures
     * of two fields. That is said as a composing this does not do, and never as a total no row
     * reaches.
     */
    @Test
    void totalsThatReadOneFieldAreNotSaidToHaveNoRow() {
        Compilation compilation = measured(MODULE.formatted("", AMOUNT
                + "\n            && List.sum(List.map(p -> p.amount + p.fee, ps)) >= 5"));
        assertFalse(report(compilation).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(compilation));
    }

    /**
     * What is offered for the behavior is written back as its examples, each with the answer the
     * row gives, and the examples are measured: a line of either total is met only where a row
     * stands at it.
     */
    private static Compilation measuredWithItsOwnRows(String source, Predicate<Sums> answer) {
        Compilation before = measured(source);
        List<String> rows = offeredInputs(before, "both");
        assertFalse(rows.isEmpty(), () -> "rows are offered: " + report(before));
        StringBuilder examples = new StringBuilder("\nexample both\n");
        for (int row = 0; row < rows.size(); row++) {
            examples.append("    | \"offered ").append(row).append("\" : (").append(rows.get(row))
                    .append(") -> ").append(answer.test(Sums.of(rows.get(row)))).append("\n");
        }
        return measured(source + examples);
    }

    private static List<String> offeredInputs(Compilation compilation, String behavior) {
        return Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.ledger"))
                .rowsByBehavior().getOrDefault(behavior, List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    /** The points of the lines drawn that no row is shown to be at, by name. */
    private static List<String> unmetOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        unmet(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static void unmet(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("point") && node.has("disposition")
                && !node.path("disposition").asString().equals("met")) {
            out.add(node.path("point").asString().toUpperCase(Locale.ROOT));
        }
        node.forEach(child -> unmet(child, out));
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + source);
        return compilation;
    }
}
