package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk adding the decimals of a list to a seed one at a time can stop at any step for want of
 * room, which is no fact of the total it comes to. It is told as the walk it is, and a row is
 * asked to get past every step of it, so a relation over its total is read as the same relation
 * over a total given as an input is. A step that works out anything beside adding the element is
 * no such walk, and tells nothing.
 */
class AWalkAddingDecimalsCompletesStepByStepTest {

    private static final String DECLARATIONS = """
            data Amount = Decimal
                invariant value >= 0.0m
            data Note = { gross: Amount }
            """;

    private static final String INPUTS =
            "gross: Amount, existing: List<Note>, net: Amount, tax: Amount";

    private static final Set<String> THE_FOUR_TERMS =
            Set.of("List.sum(existing[*].gross)", "gross", "net", "tax");

    private static String report(String inputs, String body) {
        return report("", inputs, body);
    }

    private static String report(String helpers, String inputs, String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                %s
                %s
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(DECLARATIONS, helpers, inputs,
                inputs.replaceAll(": (List<[^>]*>|[A-Za-z<>]+)", ""), body), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The places the report says the comparison relates rather than divides. */
    private static Set<String> related(String report) {
        return placesSaying(report, "· no line", "rather than dividing the values here");
    }

    /** The places the report says the comparison relates to a value not shown to reach them. */
    private static Set<String> notShown(String report) {
        return placesSaying(report, "· not read", "not shown to reach every value here");
    }

    private static Set<String> placesSaying(String report, String start, String words) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith(start) && line.contains(words))
                .map(line -> line.substring(line.lastIndexOf("about `") + 7, line.length() - 1))
                .collect(Collectors.toSet());
    }

    /** The comparison of the issue, over what the walk with {@code step} from {@code seed} over
     *  {@code existing} comes to. */
    private static String credited(String step, String seed) {
        return """
                {
                    let credited = List.fold((acc, n) -> %s, %s, existing)
                    Decimal.compare(Decimal.add(net.value, tax.value),
                                    Decimal.subtract(gross.value, credited)) <= 0
                }""".formatted(step, seed);
    }

    @Test
    void aRelationOverTheWalksTotalIsReadAsOverATotalGivenAsAnInput() {
        String given = report("gross: Amount, credited: Amount, net: Amount, tax: Amount", """
                Decimal.compare(Decimal.add(net.value, tax.value),
                                Decimal.subtract(gross.value, credited.value)) <= 0""");
        assertEquals(Set.of("credited", "gross", "net", "tax"), related(given), given);

        String walked = report(INPUTS, credited("Decimal.add(acc, n.gross.value)", "0.0m"));
        assertEquals(THE_FOUR_TERMS, related(walked), walked);
        assertEquals(Set.of(), notShown(walked), walked);
    }

    /** A walk a helper works out is worked out where the helper is called. */
    @Test
    void aWalkInAHelperIsTheSameWalk() {
        String walked = report("""
                let creditedSoFar (existing: List<Note>): Decimal =
                    List.fold((acc, n) -> Decimal.add(acc, n.gross.value), 0.0m, existing)
                """, INPUTS, """
                {
                    let credited = creditedSoFar(existing)
                    Decimal.compare(Decimal.add(net.value, tax.value),
                                    Decimal.subtract(gross.value, credited)) <= 0
                }""");
        assertEquals(THE_FOUR_TERMS, related(walked), walked);
    }

    /** The answer so far on either side of the sum is the same step, and a seed at another
     *  scale is the same walk. */
    @Test
    void theStepIsTheSameWhicheverSideTheAnswerSoFarIsOn() {
        for (String step : List.of("Decimal.add(n.gross.value, acc)", "acc + n.gross.value")) {
            for (String seed : List.of("0.0m", "0m")) {
                String walked = report(INPUTS, credited(step, seed));
                assertEquals(THE_FOUR_TERMS, related(walked), () -> step + " " + seed + walked);
            }
        }
    }

    /**
     * A step that works out more than the sum, even what nothing then reads, is worked out on
     * every step of the walk: nothing is told of that, so nothing is told of the walk. A product
     * by one adds the same number and works out a product all the same.
     */
    @Test
    void aStepThatWorksOutMoreThanTheSumTellsNothing() {
        for (String step : List.of(
                "Decimal.add(acc, Decimal.multiply(n.gross.value, 2.0m))",
                "Decimal.add(acc, Decimal.multiply(n.gross.value, 1.0m))",
                "Decimal.add(Decimal.add(acc, 0.0m), n.gross.value)",
                """
                {
                        let unused = Decimal.multiply(n.gross.value, 2.0m)
                        Decimal.add(acc, n.gross.value)
                    }""")) {
            String walked = report(INPUTS, credited(step, "0.0m"));
            assertEquals(Set.of(), related(walked), () -> step + walked);
        }
    }

    /** What is worked out of the walk's answer is told after it, and a row gets past both. */
    @Test
    void anOperationOverTheWalksAnswerIsToldAfterTheWalk() {
        String walked = report(INPUTS, """
                {
                    let credited = List.fold((acc, n) -> Decimal.add(acc, n.gross.value), 0.0m,
                                             existing)
                    Decimal.compare(Decimal.add(net.value, tax.value),
                                    Decimal.subtract(gross.value,
                                                     Decimal.multiply(credited, 2.0m))) <= 0
                }""");
        assertEquals(THE_FOUR_TERMS.stream().filter(each -> !each.startsWith("List.sum"))
                .collect(Collectors.toSet()), related(walked).stream()
                .filter(each -> !each.startsWith("List.sum")).collect(Collectors.toSet()),
                walked);
    }
}
