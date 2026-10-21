package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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

    /**
     * The number is the computation, whichever way an author wrote it; and two computations over
     * one list are two numbers, read beside the spellings of the one so that a reading that took
     * every total of the field for one number is told apart.
     */
    @Test
    void aFormOfOneFieldIsTheSameNumberHoweverItIsWritten() {
        Map<String, String> read = readEach(List.of("a.q * 2", "2 * a.q", "a.q + a.q", "a.q * 3"));
        String thrice = read.remove("a.q * 3");
        read.forEach((spelled, report) -> {
            assertTrue(report.contains("List.sum({2·q + 0 | xs[*]})"),
                    () -> spelled + " is twice the field: " + report);
            assertFalse(report.contains("not read"), () -> spelled + " is read: " + report);
        });
        assertTrue(thrice.contains("List.sum({3·q + 0 | xs[*]})"), thrice);
        assertFalse(thrice.contains("{2·q"), thrice);
    }

    /**
     * What the report says of each of {@code closures}, each summed over the list and compared
     * against four in a behavior of its own: the behaviors are one module, measured once, and each
     * closure is read off its own behavior's part of the report.
     */
    private static Map<String, String> readEach(List<String> closures) {
        StringBuilder module = new StringBuilder("""
                module example.computed

                data Many
                data Few

                data A = { q: Int, p: Int, debit: Bool }
                """);
        for (int at = 0; at < closures.size(); at++) {
            module.append("""

                    behavior decide%d : (xs: List<A>) -> Many | Few

                    let decide%d (xs) =
                        if List.sum(List.map(a -> %s, xs)) >= 4
                        then Many else Few
                    """.formatted(at, at, closures.get(at)));
        }
        String report = report(module.toString());
        Map<String, StringBuilder> parts = new LinkedHashMap<>();
        StringBuilder part = null;
        for (String line : report.lines().toList()) {
            Matcher behavior = BEHAVIOR.matcher(line);
            if (behavior.find()) {
                part = parts.computeIfAbsent(closures.get(Integer.parseInt(behavior.group(1))),
                        _ -> new StringBuilder());
            } else if (line.isBlank()) {
                part = null;
            }
            if (part != null) {
                part.append(line).append('\n');
            }
        }
        assertEquals(new LinkedHashSet<>(closures), parts.keySet(), report);
        Map<String, String> out = new LinkedHashMap<>();
        parts.forEach((closure, said) -> out.put(closure, said.toString()));
        return out;
    }

    /** The line a behavior's part of the report opens with. */
    private static final Pattern BEHAVIOR = Pattern.compile("^  decide(\\d+) ");

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

    /** Arithmetic over a choice by a flag is the choice of the arithmetic, in each branch. */
    @Test
    void arithmeticOverAChoiceIsTheChoiceOfTheArithmetic() {
        String weighed = report(model("(if a.debit then a.q else 0 - a.q) * 2 + a.p", 3));
        assertTrue(weighed.contains("List.sum({if debit then 1·p + 2·q + 0 else 1·p + -2·q + 0"
                + " | xs[*]})"), weighed);
        assertFalse(weighed.contains("not read"), weighed);
    }

    /**
     * Choices added up are held side by side, each made for the element on its own, and are one
     * number whichever is written first.
     */
    @Test
    void twoChoicesInOneSumAreHeldSideBySideInEitherOrder() {
        String first = "(if a.debit then a.q else 0)";
        String second = "(if a.first then a.p else 0)";
        String one = report(twoFlags(first + " + " + second + " + 1"));
        String other = report(twoFlags("1 + " + second + " + " + first));
        String read = "List.sum({1·(if debit then 1·q + 0 else 0) + 1·(if first then 1·p + 0"
                + " else 0) + 1 | xs[*]})";
        assertTrue(one.contains(read), one);
        assertTrue(other.contains(read), other);
    }

    /**
     * As many choices as are written, and no more: a sum of three of them, each on a flag of its
     * own, is three choices and not the eight ways they can fall out together.
     *
     * <p>Three and not more, because what is asked is the shape and not the size: the ways they
     * fall out together, written as choices, would each name a flag more than once, which the
     * count below tells from one choice a flag at any number of them from two up.
     */
    @Test
    void aSumOfManyChoicesIsAsLargeAsWhatWasWritten() {
        int many = 3;
        StringBuilder fields = new StringBuilder("q: Int");
        List<String> terms = new ArrayList<>();
        for (int i = 1; i <= many; i++) {
            fields.append(", f").append(i).append(": Bool");
            terms.add("(if a.f" + i + " then a.q else 0)");
        }
        String report = report("""
                module example.computed

                data Many
                data Few

                data A = { %s }

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.sum(List.map(a -> %s, xs)) >= 3
                    then Many else Few
                """.formatted(fields, String.join(" + ", terms)));
        int from = report.indexOf("List.sum({");
        int to = report.indexOf(" | xs[*]})", from);
        assertTrue(from >= 0 && to > from, report);
        String computed = report.substring(from, to);
        for (int i = 1; i <= many; i++) {
            assertTrue(computed.contains("1·(if f" + i + " then 1·q + 0 else 0)"), computed);
        }
        assertEquals(many, computed.split("if f", -1).length - 1,
                () -> "each choice once: " + computed);
    }

    /**
     * What a sum of choices can come to is what each of them can, added: at or above nought where
     * every part is, and open below where one part reaches there.
     */
    @Test
    void aSumOfChoicesIsBoundedByWhatEachPartCanComeTo() {
        String held = report(boundedChoices("Amount"));
        assertTrue(held.contains("no OUT point is owed at List.sum({1·(if debit then 1·q + 0"
                + " else 0) + 1·(if first then 1·p + 0 else 0) + 0 | xs[*]}) = 0"), held);

        String open = report(boundedChoices("Credit"));
        assertTrue(open.contains("List.sum({1·(if debit then 1·q + 0 else 0)"), open);
        assertFalse(open.contains("no OUT point is owed at List.sum("), open);
    }

    /** {@code q} at or above nought, and {@code p} of {@code pType}. */
    private static String boundedChoices(String pType) {
        return """
                module example.computed

                data Amount = Int
                    invariant value >= 0

                data Credit = Int
                    invariant value >= -5

                data Ok = { n: Int }
                data Bad

                data A = { q: Amount, p: %s, debit: Bool, first: Bool }

                behavior settle : (xs: List<A>) -> Ok | Bad
                    constructs Ok

                let settle (xs) = {
                    guard List.sum(List.map(a -> (if a.debit then a.q.value else 0)
                        + (if a.first then a.p.value else 0), xs)) > 0 else Bad
                    Ok { n = 1 }
                }
                """.formatted(pType);
    }

    private static String twoFlags(String closure) {
        return """
                module example.computed

                data Many
                data Few

                data A = { q: Int, p: Int, debit: Bool, first: Bool }

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.sum(List.map(a -> %s, xs)) >= 3
                    then Many else Few
                """.formatted(closure);
    }

    /** A fold whose step adds a choice of the element is the total of that choice. */
    @Test
    void aFoldAddingAChoiceIsTheTotalOfTheChoice() {
        String folded = report("""
                module example.computed

                data Many
                data Few

                data A = { q: Int, p: Int, debit: Bool }

                behavior decide : (xs: List<A>) -> Many | Few

                let decide (xs) =
                    if List.fold((acc, a) -> acc + (if a.debit then a.q else 0 - a.q), 0, xs) >= 3
                    then Many else Few
                """);
        assertTrue(folded.contains("List.sum({if debit then 1·q + 0 else -1·q + 0 | xs[*]})"),
                folded);
        assertFalse(folded.contains("not read"), folded);
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
        readEach(List.of("a.q", "a.q * 1", "a.q + 0", "if a.debit then a.q else a.q"))
                .forEach((spelled, report) -> {
                    assertTrue(report.contains("List.sum(xs[*].q)"), () -> spelled + ": " + report);
                    assertFalse(report.contains("List.sum({"), () -> spelled + ": " + report);
                });
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
        assertTrue(report.contains("made of several fields, chosen by a flag, chosen by their"
                + " case or chosen by where they stand"), report);
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
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Each model measured once for the class: some are asked for their report and for their
     *  rows. The rows ask what they read of the measurement; the rest is asked where a report is
     *  made. */
    private static Compilation compiled(String model) {
        return MEASURED.computeIfAbsent(model, each -> {
            Compilation compilation = Compilation.ofSource(each, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            return compilation;
        });
    }

    private static final Map<String, Compilation> MEASURED = new HashMap<>();

    /** And given back when the class is done with them: a fork keeps its JVM, so what is held
     *  statically is held for every class after this one. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }
}
