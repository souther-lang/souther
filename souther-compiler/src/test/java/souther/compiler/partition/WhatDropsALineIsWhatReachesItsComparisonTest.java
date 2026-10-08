package souther.compiler.partition;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison's line stands exactly where the values that reach the comparison reach the line.
 *
 * <p>Not where both its outcomes are ones something takes, which is the question that used to be
 * asked and is a different one. The two cases the difference shows in are opposites and had the same
 * answer: a guard under a stricter guard draws its line through values that all stop short of it,
 * and a comparison the declarations settle one way is arrived at by every row there is and takes the
 * other way out. Each has exactly one outcome nothing takes.
 *
 * <p>Only a proof drops a line. What the declarations leave, what the way states and what the walk
 * publishes about what arrives each over-approximate the rows that arrive, so a line the region
 * holding all three holds no row at is a line no arriving row reaches; the other direction is not
 * claimed.
 */
class WhatDropsALineIsWhatReachesItsComparisonTest {

    /** The sentence a document writes for a line the rows that arrive stop short of. */
    private static final String NOTHING_ARRIVES =
            "no row that arrives at it holds a value at its line";

    private static String reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /**
     * How many lines this report dropped for nothing arriving at them.
     *
     * <p>Counted by the comparison and not by the sentence. A line over two positions is said at
     * each of them, and it is one line.
     */
    private static long droppedForNothingArriving(String source) {
        return reportOf(source).lines().filter(each -> each.contains(NOTHING_ARRIVES))
                .map(each -> {
                    Matcher at = COMPARISON.matcher(each);
                    return at.find() ? at.group() : each;
                })
                .distinct().count();
    }

    /** Where a sentence about a comparison says the comparison is. */
    private static final Pattern COMPARISON = Pattern.compile("comparison@\\d+:\\d+");

    private static final String AMOUNT = """
            module d

            data Amount = Int invariant value >= 0 && value <= 1000000
            data Free
            data Charged = { yen: Int }
            """;

    /**
     * The first case: a guard the guard above it has already ruled out.
     *
     * <p>Everything that reaches the second comparison is under five thousand, so the line at six
     * thousand parts values none of which get there, and the two rows it would ask for are rows
     * nobody can write.
     */
    @Test
    void aLineTheGuardsAboveItRuleOutIsDropped() {
        assertEquals(1, droppedForNothingArriving(AMOUNT + """
                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged

                let charge (a) = {
                    guard a.value < 5000 else Free
                    guard a.value < 6000 else Free
                    Charged { yen = 500 }
                }
                """));
    }

    /**
     * The second case, which is the same shape and the opposite answer.
     *
     * <p>A {@code Level} is ten or more, so the comparison inside the body cannot hold — and every
     * row arrives at it and takes it the other way. There is a row to write at the line, so the
     * border stands: what the declarations rule out is one of the comparison's outcomes and not its
     * line.
     */
    @Test
    void aLineTheDeclarationsSettleOneWayStands() {
        String report = reportOf("""
                module example.empty

                data Level = Int invariant value >= 10
                data Answer = { n: Int }

                behavior classify : (level: Level) -> Answer
                    constructs Answer

                let classify (level) =
                    if level.value < 10 then Answer { n = 1 } else Answer { n = 2 }
                """);

        assertEquals(0, report.lines().filter(each -> each.contains(NOTHING_ARRIVES)).count(),
                () -> "every row arrives at this comparison and takes it the other way: " + report);
        assertTrue(report.contains("level = 10 (comparison"),
                () -> "so the line at ten is one the measure asks about, and it is the"
                        + " comparison's own and not only the clause's: " + report);
    }

    /**
     * A path nothing reaches, with the compared position's own values untouched.
     *
     * <p>Whether anything arrives is the whole state's answer and never a projection of it. The
     * guard above asks for an amount past where an {@code Amount} stops, so nothing stands below it
     * — and none of that reaches what is known of {@code b.value}, which still runs from nought to a
     * million with the line at five thousand well inside. Read as an interval of the position the
     * comparison turns on, this line is one every row reaches; read as what arrives, no row does.
     *
     * <p>The guard above is a line of its own and is dropped for its own reason: the declarations
     * never run that far, which is a fact about them and holds wherever the rule stands. So the one
     * sentence counted here is the second comparison's.
     */
    @Test
    void aPathNothingReachesDropsTheLinesBelowItWhateverTheirOwnValuesAre() {
        assertEquals(1, droppedForNothingArriving("""
                module d

                data Amount = Int invariant value >= 0 && value <= 1000000
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount, b: Amount) -> Free | Charged
                    constructs Charged

                let charge (a, b) = {
                    guard a.value > 2000000 else Free
                    guard b.value < 5000 else Free
                    Charged { yen = 500 }
                }
                """));
    }

    /**
     * A value singled out is held to the same law, and the law reaches it because the decision is
     * taken where the rule is read.
     *
     * <p>Nothing that arrives at the second equality is anything but nought, so the value it names
     * is in no class of anything: the model draws the distinction and no row can stand either side
     * of it. Dropped a stage later this was never asked, because that stage only ever looked at the
     * lines that order values around them.
     */
    @Test
    void aValueSingledOutWhereNothingArrivesAtItIsDroppedToo() {
        assertEquals(1, droppedForNothingArriving(AMOUNT + """
                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged

                let charge (a) = {
                    guard a.value == 0 else Free
                    guard a.value == 5000 else Free
                    Charged { yen = 500 }
                }
                """));
    }

    /**
     * A hole the way leaves is a line nothing arrives at, as an end is.
     *
     * <p>Every row reaching the inner equality holds {@code n /= 5}, so the value it singles out is
     * one none of them holds. The ends of what arrives run from one end of the order to the other
     * and say nothing about five; what the way states does. The outer comparison's line is reached
     * from both sides and stands.
     */
    @Test
    void aHoleTheWayLeavesAtTheLineIsALineNothingArrivesAt() {
        assertEquals(1, droppedForNothingArriving("""
                module d

                behavior below : (n: Int) -> String
                let below (n) =
                    if n /= 5 then (if n == 5 then "never" else "other") else "five"
                """));
    }

    /**
     * A line naming a value is asked whether a row stands at it, whatever the value is a value of.
     *
     * <p>The question is one equation against everything that holds of a row there, so the same
     * hole answers it on a multiple of the position, on a position whose order fills — where values
     * come as near five as anyone likes and none is five — and on a sum of two positions the way
     * held apart from the value. Asked of how far the quantity runs, each of them runs straight
     * through the hole.
     */
    @Test
    void aLineNamingAValueIsAskedWhetherARowStandsAtItWhateverItIsAValueOf() {
        assertEquals(1, droppedForNothingArriving("""
                module d

                behavior below : (n: Int) -> String
                let below (n) =
                    if n /= 5 then (if 2 * n == 10 then "never" else "other") else "five"
                """), "on a multiple of the position");
        assertEquals(1, droppedForNothingArriving("""
                module d

                behavior below : (x: Decimal) -> String
                let below (x) =
                    if x /= 5m then (if x == 5m then "never" else "other") else "five"
                """), "on an order that fills");
        assertEquals(1, droppedForNothingArriving("""
                module d

                behavior below : (a: Int, b: Int) -> String
                let below (a, b) =
                    if a + b /= 10 then (if a + b == 10 then "never" else "other") else "ten"
                """), "on a sum of two positions");
    }

    /**
     * And a hole takes no line away from a rule that orders the values around it.
     *
     * <p>Under {@code n /= 5}, {@code n >= 5} still parts four from six: rows on both sides arrive
     * and go different ways. The control for the hole above, which takes away the line of a rule
     * naming the value and nothing else.
     */
    @Test
    void aHoleAtTheLineOfAnOrderingLeavesItDividing() {
        assertEquals(0, droppedForNothingArriving("""
                module d

                behavior below : (n: Int) -> String
                let below (n) =
                    if n /= 5 then (if n >= 5 then "above" else "below") else "five"
                """));
    }

    /**
     * The declarations are asked the same question, so a value they hold a position apart from is
     * a value no line naming it is drawn at.
     *
     * <p>Where the comparison is read and nothing is on the way, the region is what the
     * declarations leave, and a {@code Level} is never five. Asked how far the values run, the line
     * at five was inside them.
     */
    @Test
    void aValueTheDeclarationsHoldAPositionApartFromIsNoLine() {
        String report = reportOf("""
                module d

                data Level = Int invariant value /= 5
                behavior f : (x: Level) -> String
                let f (x) = if x.value == 5 then "never" else "other"
                """);

        assertTrue(report.contains("draws its line outside"),
                () -> "no Level is five, so the equality draws no line: " + report);
    }

    /**
     * A case an arm leaves out is a hole on the order the cases stand on, and a line at it is one
     * nothing arrives at.
     *
     * <p>The same question as the numeric hole above and the same answer, for the same reason: what
     * the narrowing states is the places of the order it leaves out, and a line at one of them is a
     * line no row past the arm holds a value at. Narrowed to one case or to a sum of several, which
     * leave different places out.
     */
    @Test
    void aCaseAnArmLeavesOutIsALineNothingArrivesAt() {
        String levels = """
                module d

                data Low
                data Mid
                data High
                data Lowish = Low | Mid
                data Level = Lowish | High
                data R = { level: Level }

                behavior f : (r: R) -> String
                """;
        assertEquals(1, droppedForNothingArriving(levels + """
                let f (r) =
                    match r.level with
                        | Low -> (if r.level == Mid then "never" else "low")
                        | Mid -> "mid"
                        | High -> "high"
                """));
        assertEquals(1, droppedForNothingArriving(levels + """
                let f (r) =
                    match r.level with
                        | Lowish -> (if r.level == High then "never" else "low")
                        | High -> "high"
                """));
    }

    /**
     * A line on a multiple of the position is asked the same question, and nothing arriving reaches
     * it.
     *
     * <p>Every row past the first guard holds {@code a.value < 2500}, so twice it stops short of six
     * thousand. The quantity is not the position's own value, and what the way states is about the
     * row and not about a projection onto one position — so the line on the multiple is answered
     * the way a line on the position is.
     */
    @Test
    void aLineOnAMultipleOfThePositionIsAskedTheSameQuestion() {
        assertEquals(1, droppedForNothingArriving(AMOUNT + """
                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged

                let charge (a) = {
                    guard a.value < 2500 else Free
                    guard 2 * a.value < 6000 else Free
                    Charged { yen = 500 }
                }
                """));
    }

    /**
     * Where a rule on a multiple leaves off is asked on the order the rule wrote, the one its range
     * is on.
     *
     * <p>{@code 2 * a.value < 6000} leaves off at {@code a = 2999}, which the form it wrote calls
     * 5998. Every row arriving at it is there or below and takes it the true way, so the line is
     * the same line {@code a.value < 3000} draws and stands as that one does — asked whether the
     * form runs as far as 2999, the rows past the way at five thousand and up would say no.
     */
    @Test
    void whereARuleOnAMultipleLeavesOffIsOnTheOrderItWrote() {
        assertEquals(0, droppedForNothingArriving(AMOUNT + """
                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged

                let charge (a) = {
                    guard a.value >= 2500 && a.value < 3000 else Free
                    guard 2 * a.value < 6000 else Free
                    Charged { yen = 500 }
                }
                """));
    }

    /**
     * And the same holds where nothing on the way narrows anything and the declarations stop at
     * where the rule leaves off.
     *
     * <p>A {@code Window} runs to 2999 and the rule keeps every one of them, so its line is a line
     * the quantity reaches, on its kept side. Asked at 2999 of a form running from four thousand,
     * it was reported as a line drawn outside what the quantity ever holds.
     */
    @Test
    void aRuleOnAMultipleTheDeclarationsReachIsALine() {
        String report = reportOf("""
                module d

                data Window = Int invariant value >= 2000 && value <= 2999
                behavior f : (x: Window) -> String
                let f (x) = if 2 * x.value < 6000 then "a" else "b"
                """);

        assertFalse(report.contains("draws its line outside"),
                () -> "the form reaches 5998, where the rule leaves off: " + report);
        assertTrue(report.contains("comparison@"),
                () -> "the line is one the measure asks rows of: " + report);
    }

    /**
     * A line stands or falls the same however the rule is spelled.
     *
     * <p>{@code a.value >= 1001} and {@code a.value > 1000} draw one line between 1000 and 1001.
     * Every row past the first guard is at 1000 or below, so a row at 1000 arrives at the line and
     * takes the second guard the false way — whichever side of the line the number the rule wrote
     * is on.
     */
    @Test
    void aLineStandsTheSameHoweverTheRuleIsSpelled() {
        for (String second : List.of("a.value >= 1001", "a.value > 1000")) {
            assertEquals(0, droppedForNothingArriving(AMOUNT + """
                    behavior charge : (a: Amount) -> Free | Charged
                        constructs Charged

                    let charge (a) = {
                        guard a.value <= 1000 else Free
                        guard %s else Free
                        Charged { yen = 500 }
                    }
                    """.formatted(second)), second);
        }
    }

    /**
     * A line over several positions that a row past the way reaches stands.
     *
     * <p>{@code a.value} stops below five thousand and {@code b.value} does not, so the sum reaches
     * six thousand at {@code a = 0, b = 6000}. The control for the multiple above: the same way, a
     * quantity it does not keep from the line.
     */
    @Test
    void aLineOverSeveralPositionsThatTheWayLeavesRoomForStands() {
        assertEquals(0, droppedForNothingArriving("""
                module d

                data Amount = Int invariant value >= 0 && value <= 1000000
                data Free
                data Charged = { yen: Int }

                behavior charge : (a: Amount, b: Amount) -> Free | Charged
                    constructs Charged

                let charge (a, b) = {
                    guard a.value < 5000 else Free
                    guard a.value + b.value < 6000 else Free
                    Charged { yen = 500 }
                }
                """));
    }

    /**
     * The right side of a short circuit stands under the left, and the arrival says so.
     *
     * <p>{@code &&} reaches its right operand having held on the left, so the same pair of lines one
     * under the other is the same pair of answers whether they are written as two guards or as one.
     * Published from the state at the top of the condition instead, the second line would have been
     * read against everything the declarations leave.
     */
    @Test
    void theRightSideOfAShortCircuitStandsUnderTheLeft() {
        assertEquals(1, droppedForNothingArriving(AMOUNT + """
                behavior charge : (a: Amount) -> Free | Charged
                    constructs Charged

                let charge (a) = {
                    guard a.value < 5000 && a.value < 6000 else Free
                    Charged { yen = 500 }
                }
                """));
    }

    /**
     * One comparison written once and reached twice is two arrivals, and they do not merge.
     *
     * <p>A helper's comparison is a site per call, and what has been established on the way to each
     * call is the caller's own. Keyed on the comparison a person wrote, the guard above one call
     * would take the line away from the other — so the helper's line is dropped where it is reached
     * through {@code a} and still drawn where it is reached through {@code b}.
     *
     * <p>The guard over the helper's answer for {@code a} states {@code a < 6000}, read through
     * what the helper answers in each case, and nothing arrives at that line either: it is the
     * other line dropped here, and it is the guard's own.
     */
    @Test
    void oneComparisonReachedTwiceIsTwoArrivals() {
        String report = reportOf("""
                module d

                data Amount = Int invariant value >= 0 && value <= 1000000
                data Free
                data Charged = { yen: Int }

                let over (n: Int): Int = if n < 6000 then 0 else 1

                behavior charge : (a: Amount, b: Amount) -> Free | Charged
                    constructs Charged

                let charge (a, b) = {
                    guard a.value < 5000 else Free
                    guard over(a.value) == 0 else Free
                    guard over(b.value) == 0 else Free
                    Charged { yen = 500 }
                }
                """);
        List<String> dropped = report.lines().filter(each -> each.contains(NOTHING_ARRIVES))
                .toList();
        assertTrue(dropped.stream().anyMatch(each -> each.contains("comparison@7:31")
                        && each.endsWith("about `a`")),
                () -> "the helper's line, reached through a, is dropped: " + report);
        assertTrue(report.contains("ON point (comparison@7:31)"),
                () -> "and reached through b it is still drawn: " + report);
        assertTrue(dropped.stream().anyMatch(each -> each.contains("comparison@14:25")),
                () -> "the guard over what the helper answers for a states a < 6000: " + report);
        assertEquals(2, dropped.size(), () -> "and nothing else is dropped: " + dropped);
    }
}
