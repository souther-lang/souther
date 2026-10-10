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
 * A total of what a walk computed of each element is a number a rule is read about, as a total of
 * what the elements hold is.
 *
 * <p>{@code List.sum(List.map(a -> a.q * 2, xs))} came back as a rule nothing read, though
 * {@code List.sum(List.map(a -> a.q, xs))} did not: the closure answered no place of its element,
 * and a place was the only thing a run could be made of. What is held here is that the number is
 * named by the computation and not by how it was written, that the line it draws owes its points,
 * that rows are written for it and come to what they were written for, and that what is not a form
 * of the element's fields is still reported as unread.
 */
class ASumOverWhatAWalkComputedIsReadLikeASumOverWhatItReadTest {

    private static String model(String closure, int threshold) {
        return """
                module example.computed

                data Many
                data Few

                data A = { q: Int, p: Int, debit: Bool }

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.sum(List.map(a -> %s, xs)) >= %d
                    then Many else Few
                """.formatted(closure, threshold);
    }

    /** The number is the computation, whichever way an author wrote it. */
    @Test
    void aFormOfOneFieldIsTheSameNumberHoweverItIsWritten() {
        for (String spelled : List.of("a.q * 2", "2 * a.q", "a.q + a.q")) {
            String report = report(model(spelled, 4));
            assertTrue(report.contains("List.sum({2·q + 0 | xs[*]})"),
                    () -> spelled + " is twice the field: " + report);
            assertFalse(report.contains("not read"), () -> spelled + " is read: " + report);
        }
    }

    /** A name given the computation, and a helper that computes it, are the same number. */
    @Test
    void aNameGivenTheComputationDoesNotChangeTheNumber() {
        String named = """
                module example.computed

                data Many
                data Few

                data A = { q: Int, p: Int, debit: Bool }

                let doubled (a: A): Int = a.q * 2

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.sum(List.map(a -> doubled(a), xs)) >= 4
                    then Many else Few
                """;
        String report = report(named);
        assertTrue(report.contains("List.sum({2·q + 0 | xs[*]})"), report);
    }

    /** Two computations over one list are two numbers. */
    @Test
    void twoComputationsOverOneListAreTwoNumbers() {
        String report = report(model("a.q * 3", 4));
        assertTrue(report.contains("List.sum({3·q + 0 | xs[*]})"), report);
        assertFalse(report.contains("{2·q"), report);
    }

    /** More than one field, and a choice by a flag the element holds, are read. */
    @Test
    void severalFieldsAndAChoiceByAFlagAreRead() {
        String several = report(model("a.q + a.p", 3));
        assertTrue(several.contains("List.sum({1·p + 1·q + 0 | xs[*]})"), several);

        String chosen = report(model("if a.debit then a.q else 0 - a.q", 3));
        assertTrue(chosen.contains(
                "List.sum({if debit then 1·q + 0 else -1·q + 0 | xs[*]})"), chosen);
        assertFalse(chosen.contains("not read"), chosen);
    }

    /**
     * A closure that is the field and nothing made of it is the place, whichever way it is spelled.
     *
     * <p>One number is one term. Held as a computation of the field in one spelling and as the
     * field in another, a rule on each would be about two numbers and no relation between the two
     * rules could be drawn.
     */
    @Test
    void aClosureThatIsTheFieldIsTheFieldWhateverItIsSpelledAs() {
        for (String spelled : List.of("a.q", "a.q * 1", "a.q + 0", "if a.debit then a.q else a.q")) {
            String report = report(model(spelled, 4));
            assertTrue(report.contains("List.sum(xs[*].q)"), () -> spelled + ": " + report);
            assertFalse(report.contains("List.sum({"), () -> spelled + ": " + report);
        }
    }

    /**
     * A closure that changes what a number is counted as is not the field, though it is the same
     * number.
     *
     * <p>A total of whole numbers and a total of the same numbers as decimals are not one total:
     * two lines of the largest whole number come to a decimal and to no whole number. Read as the
     * place, the second would be measured as the first.
     */
    @Test
    void aClosureThatChangesTheTypeOfTheFieldIsNotTheField() {
        String report = report(model("Decimal.fromInt(a.q)", 4).replace(">= 4", ">= 4.0m"));
        assertTrue(report.contains("List.sum({1·q + 0 | xs[*]})"), report);
        assertFalse(report.contains("List.sum(xs[*].q)"), report);
    }

    /**
     * A total of decimals made of whole numbers is written with whole numbers and counted as
     * decimals: no whole number is a half, and the point at one is said as one nothing was written
     * for rather than as one nothing reaches.
     */
    @Test
    void aTotalOfDecimalsMadeOfWholeNumbersIsWrittenWithWholeNumbers() {
        String rows = rowsOf(model("Decimal.fromInt(a.q)", 4).replace(">= 4", ">= 4.5m"));
        assertTrue(totalsOf(rows, 1, 0).stream().anyMatch(each -> each > 4),
                () -> "a row past the line, written with whole numbers: " + rows);
        assertTrue(rows.contains("no row for `List.sum({1·q + 0 | xs[*]}) = 4.5`"), rows);
    }

    /** The names a number is written under are not what it is counted as. */
    @Test
    void aClosureThroughANewtypeIsStillTheField() {
        String report = report("""
                module example.computed

                data Many
                data Few

                data Amount = Int
                data A = { amount: Amount }

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.sum(List.map(a -> a.amount.value * 1, xs)) >= 4
                    then Many else Few
                """);
        assertTrue(report.contains("List.sum(xs[*].amount)"), report);
        assertFalse(report.contains("List.sum({"), report);
    }

    /**
     * A name read in two branches is one definition met twice, and no cycle.
     *
     * <p>What is read is the choice with the name's own choice inside it on both sides.
     */
    @Test
    void aNameReadInTwoBranchesIsNotACycle() {
        String report = report("""
                module example.computed

                data Many
                data Few

                data A = { q: Int, debit: Bool, first: Bool, second: Bool }

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.sum(List.map(a -> {
                            let s = if a.debit then a.q else 0 - a.q
                            if a.first then s else if a.second then s else 0
                        }, xs)) >= 3
                    then Many else Few
                """);
        assertTrue(report.contains("List.sum({if first then if debit then 1·q + 0 else -1·q + 0"
                + " else if second then if debit then 1·q + 0 else -1·q + 0 else 0 | xs[*]})"),
                report);
        assertFalse(report.contains("not read"), report);
    }

    /** A weight below nought is solved for the way any other is: the fields come to minus the rest. */
    @Test
    void aNegativeWeightIsSolvedForAndReadBack() {
        List<Long> totals = totalsOf(rowsOf(model("0 - a.q * 2", 4)), -2, 0);

        assertTrue(totals.contains(4L), () -> "the point on the line: " + totals);
        assertTrue(totals.stream().anyMatch(each -> each > 4), () -> "one inside: " + totals);
        assertTrue(totals.stream().anyMatch(each -> each < 3), () -> "one outside: " + totals);
    }

    /** A product of two fields is no form of them, and stays a rule nothing read. */
    @Test
    void aProductOfTwoFieldsStaysUnread() {
        String report = report(model("a.q * a.p", 3));
        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("List.sum({"), report);
    }

    /**
     * Every point the line owes is a row, and each row comes to what its point asks for.
     *
     * <p>Read off the rows and added up here, one number apiece with its own constant: the total of
     * {@code q + 1} over a list is what the fields come to and the length of the list, and a row
     * that added the one once for the whole run would be a total that points at nothing.
     */
    @Test
    void theRowsWrittenComeToTheTotalsThePointsAskFor() {
        List<Long> totals = totalsOf(rowsOf(model("a.q + 1", 5)), 1, 1);

        assertTrue(totals.contains(5L), () -> "the point on the line: " + totals);
        assertTrue(totals.contains(4L), () -> "the point just off it: " + totals);
        assertTrue(totals.stream().anyMatch(each -> each > 5), () -> "one inside: " + totals);
        assertTrue(totals.stream().anyMatch(each -> each < 4), () -> "one outside: " + totals);
    }

    /**
     * What stands beside the field is solved for as many times as there are elements.
     *
     * <p>Where the rules leave a list at least three elements, a total of {@code q + 1} is the
     * fields' total and three: solved as though the one stood once for the run, every row would
     * come to two more than the point it was written for.
     */
    @Test
    void aConstantIsSolvedForOncePerElementWhereTheRulesAskForSeveral() {
        String rows = rowsOf("""
                module example.computed

                data Many
                data Few

                data A = { q: Int, p: Int, debit: Bool }
                data Cart = { lines: List<A> }
                    invariant List.length(lines) >= 3

                behavior decide : (c: Cart) -> Many | Few

                let decide (c) =
                    if List.sum(List.map(a -> a.q + 1, c.lines)) >= 8
                    then Many else Few
                """);
        List<Long> totals = totalsOf(rows, 1, 1);

        assertTrue(totals.contains(8L), () -> "the point on the line: " + totals);
        assertTrue(totals.contains(7L), () -> "the point just off it: " + totals);
    }

    /** A point no whole number of the field reaches is said as a point nothing was written for. */
    @Test
    void aTotalNoElementComesToIsNotSaidToBeOneNoRowComesTo() {
        String rows = rowsOf(model("a.q * 2", 4));
        assertTrue(rows.contains("no row for `List.sum({2·q + 0 | xs[*]}) = 3`"), rows);
        assertTrue(rows.contains("untried"), rows);
        assertEquals(3, totalsOf(rows, 2, 0).size(),
                () -> "the other three points have rows: " + rows);
    }

    /** What chooses more than one field of an element is a way this compiler writes none of. */
    @Test
    void aFormOfSeveralFieldsIsReadAndNoRowIsWrittenForIt() {
        String model = model("a.q + a.p", 3);
        String report = report(model);
        assertTrue(report.contains("made of several fields or chosen by a flag"), report);
        String rows = rowsOf(model);
        assertTrue(rows.contains("no row for"), rows);
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
        return compilation;
    }
}
