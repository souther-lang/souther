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
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container asked for what different fields of its elements come to: one element holds a figure
 * at each of the fields, so the elements are chosen for all the totals together and a row has to
 * meet each of them.
 */
class SeveralTotalsOfDifferentFieldsOfOneContainerAreComposedTogetherTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final Pattern POSTING = Pattern.compile("Posting \\{ ([^}]*) }");

    private static final Pattern FIGURE = Pattern.compile("(\\w+) = (-?\\d+)");

    private static final String AMOUNT = "List.sum(List.map(p -> p.amount, ps)) >= 100";

    private static final String FEE = "List.sum(List.map(p -> p.fee, ps)) >= 5";

    private static final String TAX = "List.sum(List.map(p -> p.tax, ps)) >= 2";

    private static String module(String fields, String rules, String... conditions) {
        return """
                module example.ledger

                data Posting = { %s }
                %s
                behavior both : (ps: List<Posting>) -> Bool

                let both (ps) =
                    %s
                """.formatted(fields, rules, String.join("\n        && ", conditions));
    }

    private static String twoFields(String rules, String... conditions) {
        return module("amount: Int, fee: Int", rules, conditions);
    }

    /** What the postings of an offered row come to at each field, and how many there are. */
    private record Row(Map<String, Integer> sums, int count, boolean everyElementKeepsFeeUnderAmount) {

        static Row of(String row) {
            Map<String, Integer> sums = new LinkedHashMap<>();
            int count = 0;
            boolean within = true;
            Matcher postings = POSTING.matcher(row);
            while (postings.find()) {
                Map<String, Integer> figures = new LinkedHashMap<>();
                Matcher figure = FIGURE.matcher(postings.group(1));
                while (figure.find()) {
                    int value = Integer.parseInt(figure.group(2));
                    figures.put(figure.group(1), value);
                    sums.merge(figure.group(1), value, Integer::sum);
                }
                count++;
                within &= figures.getOrDefault("fee", 0) <= figures.getOrDefault("amount", 0);
            }
            return new Row(sums, count, within);
        }

        int sum(String field) {
            return sums.getOrDefault(field, 0);
        }

        boolean meetsAmountAndFee() {
            return sum("amount") >= 100 && sum("fee") >= 5;
        }
    }

    @Test
    void rowsAreOfferedAtTheEdgesOfBothTotals() {
        Compilation compilation = measuredWithItsOwnRows(twoFields("", AMOUNT, FEE),
                Row::meetsAmountAndFee);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
        assertFalse(report(compilation).contains("no row takes a decision rule"),
                () -> report(compilation));
    }

    @Test
    void theOrderTheTotalsAreWrittenInDoesNotChooseWhichOfThemIsComposed() {
        Compilation compilation = measuredWithItsOwnRows(twoFields("", FEE, AMOUNT),
                Row::meetsAmountAndFee);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
    }

    @Test
    void aSizeAskedBesideTheTotalsIsTheSizeOfTheOneContainerTheyAreComposedFor() {
        Compilation compilation = measuredWithItsOwnRows(
                twoFields("", "List.length(ps) == 2", AMOUNT, FEE),
                row -> row.meetsAmountAndFee() && row.count() == 2);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
        assertTrue(offeredInputs(compilation, "both").stream().map(Row::of)
                        .allMatch(row -> row.count() == 2),
                () -> "every offered row holds the size asked for: " + report(compilation));
    }

    /** Not a pair: a third total is one more share of each element. */
    @Test
    void threeTotalsAreComposedTogetherAsTwoAre() {
        Compilation compilation = measuredWithItsOwnRows(
                module("amount: Int, fee: Int, tax: Int", "", AMOUNT, FEE, TAX),
                row -> row.meetsAmountAndFee() && row.sum("tax") >= 2);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
    }

    /** A total of a form of a field is solved for as a total of one alone is. */
    @Test
    void aFormOfAFieldBesideAFieldOfItsOwnIsComposedTogether() {
        Compilation compilation = measuredWithItsOwnRows(twoFields("",
                        "List.sum(List.map(p -> 2 * p.amount + 3, ps)) >= 100", FEE),
                row -> 2 * row.sum("amount") + 3 * row.count() >= 100 && row.sum("fee") >= 5);
        assertEquals(List.of(), unmetOf(compilation), () -> report(compilation));
    }

    @Test
    void whatTheElementsTypeRequiresOfAFeeBesideItsAmountIsKeptByEveryElement() {
        Compilation compilation = measured(twoFields("    invariant fee <= amount\n",
                AMOUNT, FEE));
        List<String> rows = offeredInputs(compilation, "both");
        assertFalse(rows.isEmpty(), () -> "rows are offered: " + report(compilation));
        assertTrue(rows.stream().map(Row::of).allMatch(Row::everyElementKeepsFeeUnderAmount),
                () -> "every element of an offered row keeps the rule: " + rows);
        assertTrue(rows.stream().map(Row::of).anyMatch(Row::meetsAmountAndFee),
                () -> "a row meets both totals: " + rows);
    }

    /**
     * Elements whose fee is their amount: a row meeting both totals has the one total at least as
     * large as the other, and a point of the fee's total away from that is a point no row stands
     * at. The shares of each total are spread without the other, so this does not find the rows
     * the rule leaves, and says that and not that there are none.
     */
    @Test
    void aRuleTyingTheFieldsTogetherIsSaidToBeBeyondWhatIsComposedAndNotToLeaveNoRow() {
        Compilation compilation = measured(twoFields("    invariant fee == amount\n",
                AMOUNT, FEE));
        assertFalse(report(compilation).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(compilation));
        assertFalse(unmetOf(compilation).isEmpty(), () -> report(compilation));
    }

    /**
     * The second total reads the field the first does, so the shares of the two are not figures
     * of two fields. That is said as a composing this does not do, and never as a total no row
     * reaches.
     */
    @Test
    void totalsThatReadOneFieldAreNotSaidToHaveNoRow() {
        Compilation compilation = measured(twoFields("", AMOUNT,
                "List.sum(List.map(p -> p.amount + p.fee, ps)) >= 5"));
        assertFalse(report(compilation).contains("no row can stand at the"),
                () -> "an emptiness no one established is not said: " + report(compilation));
    }

    /**
     * What is offered for the behavior is written back as its examples, each with the answer the
     * row gives, and the examples are measured: a line of any total is met only where a row
     * stands at it.
     */
    private static Compilation measuredWithItsOwnRows(String source, Predicate<Row> answer) {
        Compilation before = measured(source);
        List<String> rows = offeredInputs(before, "both");
        assertFalse(rows.isEmpty(), () -> "rows are offered: " + report(before));
        StringBuilder examples = new StringBuilder("\nexample both\n");
        for (int row = 0; row < rows.size(); row++) {
            examples.append("    | \"offered ").append(row).append("\" : (").append(rows.get(row))
                    .append(") -> ").append(answer.test(Row.of(rows.get(row)))).append("\n");
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
