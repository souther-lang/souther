package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading could not read of a condition is owed only where the condition is evaluated. A
 * part the conditions before it keep from being evaluated — the right of an {@code &&} whose left
 * is false there, a branch an earlier test turned away — owes nothing, and the same part where the
 * compiler cannot show that keeps its question.
 *
 * <p>Two readers raise such a question, a comparison of the values and a fork whose condition no
 * reader took in, and each case is asked of both. What is compared is the entry itself — the
 * position, the reason, whether the reading stopped, and how many rules it is filed under — and
 * never the positions alone, so a rule that stays cannot stand in for one that went.
 */
class AStopNoRowReachesIsNotReportedAsNotReadTest {

    private static final String MODEL = """
            module demo
            data Yes = { n: Int }
            data No = { n: Int }
            data Terms = Net15 | Net30 | Eom
            let weekday (c: Date, d: Date): Int = Int.floorMod(Date.daysBetween(c, d), 7)
            let stopped (c: Date, d: Date): Bool = weekday(c, Date.addMonths(1, d)) >= 1
            behavior f : (c: Date, d: Date, t: Terms, xs: List<Int>) -> Yes | No
            let f (c, d, t, xs) = %s
            """;

    /** The month a date moves into is a stop of the reading, whatever it is compared with. */
    private static final String STOP = "weekday(c, Date.addMonths(1, d)) >= 1";

    /** A condition no reader takes in, so the fork around it states a rule of its own. */
    private static final String OPAQUE = "List.contains(0, xs)";

    private static final String SEVERAL = "Int.max(weekday(c, Date.addMonths(1, d)),"
            + " weekday(c, d)) >= 3";

    private static final String CLOSURE = "List.any(n -> weekday(c, Date.addMonths(n, d)) >= 1,"
            + " xs)";

    private static final String YES = "Yes { n = 1 }";

    private static final String NO = "No { n = 0 }";

    /** {@code condition} where an earlier test has already turned every run away from it. */
    private static String turnedAway(String condition) {
        return "if t == Eom then " + NO + " else if t == Eom && " + condition + " then " + YES
                + " else " + NO;
    }

    /** {@code condition} where nothing is known of {@code t}, to be read against its control. */
    private static String reached(String condition) {
        return "if t == Eom && " + condition + " then " + YES + " else " + NO;
    }

    /** The control's own shape: {@code condition} on a way with nothing before it. */
    private static String plain(String condition) {
        return "if " + condition + " then " + YES + " else " + NO;
    }

    @Test
    void aComparisonThatStoppedOnAWayNoRowTakesOwesNothing() {
        assertNothingOwed(turnedAway(STOP));
    }

    @Test
    void aForkNoReaderTookInOnAWayNoRowTakesOwesNothing() {
        assertNothingOwed(turnedAway(OPAQUE));
    }

    /** Both parts of a nested condition are behind the same test, and each is asked on its own. */
    @Test
    void aPartBehindSeveralTestsOwesNothing() {
        assertNothingOwed(turnedAway("(true && " + OPAQUE + ")"));
        assertNothingOwed(turnedAway(OPAQUE + " && " + OPAQUE));
        assertNothingOwed(turnedAway("(true && " + STOP + ")"));
    }

    @Test
    void aStopInAHelperOrAClosureOnAWayNoRowTakesOwesNothing() {
        assertNothingOwed(turnedAway("stopped(c, d)"));
        assertNothingOwed(turnedAway(CLOSURE));
    }

    @Test
    void aStatementOfSeveralLinesOnAWayNoRowTakesOwesNothing() {
        assertNothingOwed(turnedAway(SEVERAL));
    }

    /** The arm of a {@code match} the cases before it have covered is turned away the same way. */
    @Test
    void aStopInAnArmOnlyAnEarlierTestCouldTakeOwesNothing() {
        assertNothingOwed("match t with | Eom -> " + NO + " | Net15 -> if t == Eom && " + STOP
                + " then " + YES + " else " + NO + " | Net30 -> " + NO);
    }

    @Test
    void aStopInABranchNoRunEntersOwesNothing() {
        assertNothingOwed("if t == Eom then " + NO + " else if t == Eom && true then (if " + STOP
                + " then " + YES + " else " + NO + ") else " + NO);
    }

    /**
     * The same conditions where the compiler cannot show the way empty keep what they owe, and owe
     * what the same condition owes with nothing before it: the proof is the only thing that
     * removes the question, so a reading that grows weaker gets it back.
     */
    @Test
    void theSameConditionsOnAWayNotShownEmptyOweWhatTheyOweAlone() {
        for (String condition : List.of(STOP, OPAQUE, SEVERAL, CLOSURE, "stopped(c, d)")) {
            List<String> alone = entriesOf(plain(condition));
            assertTrue(!alone.isEmpty(), "the control owes something: " + condition);
            assertEquals(alone, entriesOf(reached(condition)), condition);
            assertEquals(alone, entriesOf("if t == Eom then " + NO + " else if " + condition
                    + " then " + YES + " else " + NO), condition);
        }
    }

    /**
     * A rule no run reaches does not take the place of one that is reached, or the other way
     * round: at the positions both name, what is owed is what the reached one owes alone.
     */
    @Test
    void aRuleNoRunReachesIsToldApartFromOneAtTheSamePositions() {
        for (String condition : List.of(STOP, OPAQUE)) {
            String both = "if " + condition + " then (" + turnedAway(condition) + ") else " + NO;
            assertEquals(entriesOf(plain(condition)), entriesOf(both), condition);
            assertEquals(1, citedRulesOf(both), condition);
        }
    }

    private static void assertNothingOwed(String body) {
        PartitionEvidence evidence = evidenceOf(body);
        assertEquals(List.of(), entriesOf(evidence), body);
        assertEquals(List.of(), evidence.unanswered(), body);
    }

    private static List<String> entriesOf(String body) {
        return entriesOf(evidenceOf(body));
    }

    private static List<String> entriesOf(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .map(each -> each.at() + " " + each.reason() + " " + each.readingStopped())
                .sorted().toList();
    }

    private static long citedRulesOf(String body) {
        return evidenceOf(body).notRead().stream()
                .flatMap(each -> each.cited().stream()).distinct().count();
    }

    private static PartitionEvidence evidenceOf(String body) {
        Compilation compilation = Compilation.ofSource(MODEL.formatted(body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), body);
        return compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f");
    }
}
