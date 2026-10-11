package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk from a seed whose step only adds to the answer so far answers the seed and the total of
 * what each element adds, so a rule about it is a rule about that total — the one a
 * {@code List.sum} of the same numbers is.
 *
 * <p>A comparison over {@code List.fold((acc, p) -> Decimal.add(acc, p.amount), 0.0m, ps)} was
 * reported as about a value made from the list and not worked out, though the same comparison over
 * {@code List.sum(List.map(p -> p.amount, ps))} drew its lines and had rows written for it. What is
 * held here is that the two are one number however the step is spelled, that the seed moves the
 * line and the weight scales it, and that a step that is anything but an addition of something the
 * element alone holds is still reported as unread.
 */
class AFoldThatOnlyAddsIsReadAsTheTotalOfWhatItAddsTest {

    private static String model(String step, String seed, int threshold) {
        return """
                module example.folded

                data Many
                data Few

                data A = { q: Int, p: Int, debit: Bool }

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.fold((acc, a) -> %s, %s, xs) >= %d
                    then Many else Few
                """.formatted(step, seed, threshold);
    }

    private static String summed(String closure, int threshold) {
        return """
                module example.folded

                data Many
                data Few

                data A = { q: Int, p: Int, debit: Bool }

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.sum(List.map(a -> %s, xs)) >= %d
                    then Many else Few
                """.formatted(closure, threshold);
    }

    /** The number is the total, whichever way the step was written. */
    @Test
    void anAdditionIsTheSameTotalHoweverItIsWritten() {
        for (String step : List.of("acc + a.q", "a.q + acc", "acc + a.q + 0", "(acc + a.q)")) {
            String report = report(model(step, "0", 4));
            assertTrue(report.contains("List.sum(xs[*].q)"), () -> step + ": " + report);
            assertFalse(report.contains("not read"), () -> step + ": " + report);
        }
    }

    /** A name given the answer so far, or what the step adds, is the same step. */
    @Test
    void aNameGivenWhatTheStepAddsIsTheSameStep() {
        String report = report(model("{ let grown = acc + a.q  grown }", "0", 4));
        assertTrue(report.contains("List.sum(xs[*].q)"), report);
        assertFalse(report.contains("not read"), report);

        String squared = report(model("{ let grown = acc * acc  grown + a.q }", "0", 4));
        assertTrue(squared.contains("not read"), squared);
        assertFalse(squared.contains("List.sum"), squared);
    }

    /** A fold and a sum of the same numbers are one number, down to the rows written for them. */
    @Test
    void aFoldAndASumOfTheSameNumbersAreWrittenTheSameRows() {
        assertEquals(rowsOf(summed("a.q", 4)), rowsOf(model("acc + a.q", "0", 4)));
        assertEquals(rowsOf(summed("a.q * 2", 4)), rowsOf(model("acc + a.q * 2", "0", 4)));
    }

    /** What the walk starts at moves the line by that much. */
    @Test
    void theSeedMovesTheLine() {
        String report = report(model("acc + a.q", "10", 14));
        assertTrue(report.contains("List.sum(xs[*].q): = 4"), report);
        assertTrue(report.contains("List.sum(xs[*].q): = 3"), report);
        assertFalse(report.contains("not read"), report);

        List<Long> totals = totalsOf(rowsOf(model("acc + a.q", "10", 14)), 1, 0);
        assertTrue(totals.contains(4L), () -> "the point on the line: " + totals);
        assertTrue(totals.contains(3L), () -> "the point just off it: " + totals);
    }

    /** A step that takes something away adds a negative number. */
    @Test
    void aSubtractionAddsTheNegativeOfWhatItTakes() {
        String report = report(model("acc - a.q", "10", 6));
        assertTrue(report.contains("List.sum({-1·q + 0 | xs[*]})"), report);
        assertFalse(report.contains("not read"), report);
    }

    /** What the step adds may be made of the element's fields, and is the same total as a sum of it. */
    @Test
    void aComputedAdditionIsTheTotalOfWhatWasComputed() {
        String report = report(model("acc + a.q * 2 + a.p", "0", 5));
        assertTrue(report.contains("List.sum({1·p + 2·q + 0 | xs[*]})"), report);
        assertFalse(report.contains("not read"), report);
    }

    /** A rule on the total over a list the rules leave empty is a rule on a total of nothing. */
    @Test
    void theRowsWrittenComeToTheTotalsThePointsAskFor() {
        List<Long> totals = totalsOf(rowsOf(model("acc + a.q", "0", 5)), 1, 0);

        assertTrue(totals.contains(5L), () -> "the point on the line: " + totals);
        assertTrue(totals.contains(4L), () -> "the point just off it: " + totals);
        assertTrue(totals.stream().anyMatch(each -> each > 5), () -> "one inside: " + totals);
        assertTrue(totals.stream().anyMatch(each -> each < 4), () -> "one outside: " + totals);
    }

    /** The same walk over decimals, and over a field a newtype wraps. */
    @Test
    void aTotalOfDecimalsAndOfAWrappedFieldIsRead() {
        String decimals = report("""
                module example.folded

                data Posting = { amount: Decimal }

                behavior positive : (ps: List<Posting>) -> Bool

                let positive (ps) =
                    Decimal.compare(List.fold((acc, p) -> Decimal.add(acc, p.amount), 0.0m, ps), 0.0m) > 0
                """);
        assertTrue(decimals.contains("List.sum(ps[*].amount)"), decimals);
        assertFalse(decimals.contains("not read"), decimals);

        String wrapped = report("""
                module example.folded

                data Amount = Int
                data Note = { gross: Amount }

                behavior over : (ns: List<Note>) -> Bool

                let over (ns) = List.fold((acc, n) -> acc + n.gross.value, 0, ns) > 100
                """);
        assertTrue(wrapped.contains("List.sum(ns[*].gross)"), wrapped);
        assertFalse(wrapped.contains("not read"), wrapped);
    }

    /** A total that is a number among others in a comparison is read as one of them. */
    @Test
    void aTotalBesideAnotherNumberIsRead() {
        String report = report("""
                module example.folded

                data Note = { gross: Int }

                behavior fits : (limit: Int, ns: List<Note>, asked: Int) -> Bool

                let fits (limit, ns, asked) =
                    asked <= limit - List.fold((acc, n) -> acc + n.gross, 0, ns)
                """);
        assertTrue(report.contains("List.sum(ns[*].gross)"), report);
        assertFalse(report.contains("not read"), report);
    }

    /**
     * What is not an addition of something the element alone holds says nothing of a total.
     *
     * <p>The answer so far moves by one for each of itself and by nothing else, which is asked of
     * the step and not of how it is written: scaled, ignored, doubled, chosen between, or added to
     * by a figure that turns on the answer so far, the answer is not the seed and a total.
     */
    @Test
    void aStepThatIsNotAnAdditionIsNotReadAsOne() {
        for (String step : List.of(
                "acc * 2 + a.q",
                "a.q",
                "acc + acc",
                "if a.q > acc then a.q else acc",
                "acc + a.q * acc",
                "acc + acc * a.q",
                // Right at an answer of nought and of one and wrong past them: the step is judged
                // for every answer, so agreeing with an addition at two of them proves nothing.
                "acc * acc + a.q",
                "acc * (acc - 1) + acc + a.q")) {
            String report = report(model(step, "0", 4));
            assertTrue(report.contains("not read"), () -> step + ": " + report);
            assertFalse(report.contains("List.sum"), () -> step + ": " + report);
        }
    }

    /** What the walk walks has to stand at a position, as what a sum totals does. */
    @Test
    void aWalkOverWhatAFilterKeptIsNotReadAsATotalOfTheList() {
        String report = report("""
                module example.folded

                data A = { q: Int }

                behavior decide : (xs: List<A>) -> Bool

                let decide (xs) =
                    List.fold((acc, a) -> acc + a.q, 0, List.filter(a -> a.q > 0, xs)) > 3
                """);
        assertFalse(report.contains("List.sum(xs[*].q)"), report);
    }

    /** What each row's elements come to, each weighing its {@code q} and adding the constant. */
    private static List<Long> totalsOf(String rows, long weight, long constant) {
        List<Long> totals = new ArrayList<>();
        Pattern element = Pattern.compile("A \\{ q = (-?\\d+)");
        // One chunk per row, which is written over as many lines as its value needs.
        for (String row : rows.split("\n    \\| ")) {
            Matcher found = element.matcher(row);
            long total = 0;
            boolean any = false;
            while (found.find()) {
                total += weight * Long.parseLong(found.group(1)) + constant;
                any = true;
            }
            if (any) {
                totals.add(total);
            }
        }
        return totals;
    }

    private static String rowsOf(String model) {
        return GeneratedRows.of(compiled(model), null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
    }

    private static String report(String model) {
        Compilation compilation = compiled(model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + model);
        return compilation;
    }
}
