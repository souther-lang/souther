package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleCitation;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading could not read of a condition is owed only where the condition is evaluated. A
 * part the conditions before it keep from being evaluated — the right of an {@code &&} whose left
 * is false there, a branch an earlier test turned away — owes nothing, and the same part where the
 * compiler cannot show that keeps its question.
 *
 * <p>Two readers raise such a question, a comparison of the values and a fork whose condition no
 * reader took in; a stopped comparison and an opaque fork are each asked, and the shapes around
 * them are asked of whichever reader their part falls to. What is compared is the entry itself —
 * the position, the reason, whether the reading stopped — and never the positions alone, so a rule
 * that stays cannot stand in for one that went.
 */
class AStopNoRowReachesIsNotReportedAsNotReadTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

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
            assertFalse(alone.isEmpty(), "the control owes something: " + condition);
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
        }
    }

    /**
     * Which rule stays is the one a run reaches. Two rules with the same position and the same
     * reason are told apart by the rule cited: the same text with the first test written so that
     * a run does reach the second rule cites both, and the text with the run turned away cites
     * only the one a run reaches, which is among them.
     */
    @Test
    void theRuleThatStaysIsOneOfTheTwoARunReaches() {
        String turnedAway = "if t == Eom then " + NO + " else if t == Eom && " + STOP + " then "
                + YES + " else (" + plain(STOP) + ")";
        String reachable = turnedAway.replace("if t == Eom then", "if t == Net15 then");
        Set<RuleCitation> both = citedBy(reachable);
        Set<RuleCitation> stays = citedBy(turnedAway);
        assertEquals(2, both.size(), "the control owes both rules");
        assertEquals(1, stays.size());
        assertTrue(both.containsAll(stays));
    }

    /**
     * And where the two stand at different positions, the positions say it: the reached rule's
     * are all that remain, in whichever order the two are written.
     */
    @Test
    void theRuleThatStaysIsTheOneARunReachesWhateverItIsAbout() {
        for (List<String> pair : List.of(List.of(OPAQUE, STOP), List.of(STOP, OPAQUE))) {
            String reachedFirst = "if " + pair.get(0) + " then (" + turnedAway(pair.get(1))
                    + ") else " + NO;
            String reachedLast = "if t == Eom then " + NO + " else if t == Eom && " + pair.get(1)
                    + " then " + YES + " else (" + plain(pair.get(0)) + ")";
            assertEquals(entriesOf(plain(pair.get(0))), entriesOf(reachedFirst), pair.toString());
            assertEquals(entriesOf(plain(pair.get(0))), entriesOf(reachedLast), pair.toString());
        }
    }

    /** A condition behind a test inside a closure is behind it as much as one outside. */
    @Test
    void aPartBehindATestInsideAClosureOwesNothing() {
        assertNothingOwed(turnedAway("List.any(n -> t == Eom && " + OPAQUE + ", [1])"));
        assertNothingOwed(turnedAway("List.any(n -> t == Eom && " + STOP + ", [1])"));
    }

    /**
     * A test written inside a closure is a statement about each application of it, and a fork's
     * part is asked only of the way every application shares. So the part behind such a test is
     * owed what it is owed alone — the question is kept where the proof is not made — while a
     * stopped comparison there is read on each application and owes nothing.
     *
     * <p>This pins the boundary and not a wish: a fork part inside a closure that only the
     * closure's own test turns away is not shown unevaluated, which is the safe side.
     */
    @Test
    void aTestInsideAClosureTurnsAwayAComparisonButKeepsAForksQuestion() {
        String turnedAwayByTheClosure = "if t == Eom then " + NO + " else if List.any(n -> t == Eom"
                + " && %s, [1]) then " + YES + " else " + NO;
        assertNothingOwed(turnedAwayByTheClosure.formatted(STOP));
        List<String> alone = entriesOf(plain("List.any(n -> t == Eom && " + OPAQUE + ", [1])"));
        assertFalse(alone.isEmpty());
        assertEquals(alone, entriesOf(turnedAwayByTheClosure.formatted(OPAQUE)));
    }

    /** The right of an {@code ||} is evaluated where its left came out false, and only there. */
    @Test
    void thePartAfterAnOrIsOwedOnlyWhereTheLeftCanComeOutFalse() {
        for (String condition : List.of(OPAQUE, STOP)) {
            assertNothingOwed("if t == Eom then (if t == Eom || " + condition + " then " + YES
                    + " else " + NO + ") else " + NO);
            List<String> alone = entriesOf(plain(condition));
            assertFalse(alone.isEmpty(), condition);
            assertEquals(alone, entriesOf("if t == Eom || " + condition + " then " + YES
                    + " else " + NO), condition);
            assertEquals(alone, entriesOf("if t == Eom then " + NO + " else if t == Eom || "
                    + condition + " then " + YES + " else " + NO), condition);
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

    /** The rules the entries are filed under, as the model names them. */
    private static Set<RuleCitation> citedBy(String body) {
        return evidenceOf(body).notRead().stream()
                .flatMap(each -> each.cited().stream())
                .collect(Collectors.toCollection(LinkedHashSet::new));
    }

    /** Each body is measured once, however many of the questions above ask about it. */
    private static PartitionEvidence evidenceOf(String body) {
        return MEASURED.computeIfAbsent(body, written -> {
            Compilation compilation = Compilation.ofSource(MODEL.formatted(written), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors(), written);
            return compilation;
        }).db().ask(new Adequacy.Coverage("demo")).value().get("f");
    }

    /** And given back when the class is done with them: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }
}
