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
import static org.junit.jupiter.api.Assertions.assertTrue;

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
            data Line = { price: Amount, qty: Amount }
            data Totals = { gross: Decimal, count: Int }
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
                inputs.replaceAll(": (Map<[^>]*>|List<[^>]*>|[A-Za-z<>]+)", ""), body), "Main");
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

    /**
     * A walk's room turns on no number of the total it adds up, so a relation of the total with
     * one other number reads the total as well: its rows far out are asked as any are.
     */
    @Test
    void aTotalComparedWithOneOtherNumberIsRead() {
        String listed = report("existing: List<Note>, c: Amount", """
                Decimal.compare(List.fold((acc, n) -> Decimal.add(acc, n.gross.value), 0.0m,
                                          existing), c.value) <= 0""");
        assertEquals(Set.of("List.sum(existing[*].gross)", "c"), related(listed), listed);
        String mapped = report("m: Map<String, Amount>, c: Amount", """
                Decimal.compare(Map.fold((acc, k, v) -> Decimal.add(acc, v.value), 0.0m, m),
                                c.value) <= 0""");
        assertEquals(Set.of("List.sum(m[*])", "c"), related(mapped), mapped);
        // A total worked out once is as bound: its scale is the elements', whatever it comes to.
        String doubled = report("existing: List<Note>, c: Amount", """
                Decimal.compare(Decimal.multiply(List.sum(List.map(n -> n.gross.value, existing)),
                                                 2.0m), c.value) <= 0""");
        assertEquals(Set.of("List.sum(existing[*].gross)", "c"), related(doubled), doubled);
    }

    /**
     * What a step adds of an element may be taken away, or be a product of its fields: the step
     * works out that product and the sum or difference, and the walk is told with both. A total
     * of what a closure makes of each element is the same walk from nought.
     */
    @Test
    void aStepTakingAwayOrAddingAProductIsTheSameWalk() {
        String takenAway = report("existing: List<Note>, c: Amount", """
                Decimal.compare(List.fold((acc, n) -> Decimal.subtract(acc, n.gross.value),
                                          100.0m, existing), c.value) <= 0""");
        assertEquals(Set.of(), notShown(takenAway), takenAway);
        assertTrue(related(takenAway).contains("List.sum(existing[*].gross)"), takenAway);
        String products = "List.sum({1·price·qty + 0 | lines[*]})";
        String walked = report("lines: List<Line>, c: Amount", """
                Decimal.compare(List.fold((acc, l) -> Decimal.add(acc,
                                              Decimal.multiply(l.price.value, l.qty.value)),
                                          0.0m, lines), c.value) <= 0""");
        assertEquals(Set.of(products, "c"), related(walked), walked);
        String summed = report("lines: List<Line>, c: Amount", """
                Decimal.compare(List.sum(List.map(l -> Decimal.multiply(l.price.value,
                                                                        l.qty.value), lines)),
                                c.value) <= 0""");
        assertEquals(Set.of(products, "c"), related(summed), summed);
    }

    /**
     * Two totals of one list, added, are named by the comparison as the one total of what each
     * element comes to. The operations read the two, which a row holds by the list it is built
     * with and not as terms of its own, and a row of one element writes what the one total takes.
     */
    @Test
    void twoTotalsOfOneListAreReadAsTheOneTotalTheComparisonNames() {
        String merged = "List.sum({1·price + 1·qty + 0 | lines[*]})";
        String summed = report("lines: List<Line>, c: Amount", """
                Decimal.compare(Decimal.add(List.sum(List.map(l -> l.price.value, lines)),
                                            List.sum(List.map(l -> l.qty.value, lines))),
                                c.value) <= 0""");
        assertEquals(Set.of(merged, "c"), related(summed), summed);
        String walked = report("lines: List<Line>, c: Amount", """
                Decimal.compare(Decimal.add(
                        List.fold((acc, l) -> Decimal.add(acc, l.price.value), 0.0m, lines),
                        List.fold((acc, l) -> Decimal.add(acc, l.qty.value), 0.0m, lines)),
                    c.value) <= 0""");
        assertEquals(Set.of(merged, "c"), related(walked), walked);
    }

    /** A total of what a closure makes of each number of a list written out is told as the
     *  library adds the answers up: from nought, one after another. */
    @Test
    void aTotalOfAClosureOverAListWrittenOutIsToldAsItIsAddedUp() {
        String report = report("a: Amount, b: Amount, c: Amount", """
                Decimal.compare(List.sum(List.map(x -> Decimal.add(x, 1.0m),
                                                  [a.value, b.value])), c.value) <= 0""");
        assertEquals(Set.of(), notShown(report), report);
        assertTrue(related(report).containsAll(Set.of("a", "b")), report);
    }

    /** A walk over a map of decimals adding the product of each value and what another map holds
     *  under its key, or nought, is a walk of products. */
    @Test
    void aWalkJoiningTwoMapsOfDecimalsIsAWalkOfProducts() {
        String report = report(
                "qty: Map<String, Decimal>, prices: Map<String, Decimal>, c: Amount", """
                Decimal.compare(Map.fold((acc, k, q) -> Decimal.add(acc, Decimal.multiply(q,
                                    Option.withDefault(0.0m, Map.get(k, prices)))), 0.0m, qty),
                                c.value) <= 0""");
        assertEquals(Set.of("List.sum({qty[*] * prices[*] under one key})", "c"), related(report),
                report);
    }

    /**
     * A field of what a walk carrying a record answers is read as that field's own walk. Every
     * field is worked out at every step, so every field's walk is told: the gross added as a walk
     * of decimals, the count by one. A field whose step does more than that tells nothing.
     */
    @Test
    void aFieldOfAWalkCarryingARecordIsToldWithEveryFieldsWalk() {
        String carried = report("existing: List<Note>, c: Amount", """
                Decimal.compare(List.fold((acc, n) -> Totals {
                                        gross = Decimal.add(acc.gross, n.gross.value),
                                        count = acc.count + 1 },
                                    Totals { gross = 0.0m, count = 0 }, existing).gross,
                                c.value) <= 0""");
        assertEquals(Set.of("List.sum(existing[*].gross)", "c"), related(carried), carried);
        String doubling = report("existing: List<Note>, c: Amount", """
                Decimal.compare(List.fold((acc, n) -> Totals {
                                        gross = Decimal.add(acc.gross, n.gross.value),
                                        count = acc.count * 2 },
                                    Totals { gross = 0.0m, count = 1 }, existing).gross,
                                c.value) <= 0""");
        assertEquals(Set.of(), related(doubling), doubling);
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
