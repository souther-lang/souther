package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation read on an arm of a choice is held by the rows that take the arm, and a row that
 * takes it has worked out what the arm works out: {@code d + 1} on the arm that adds one. The
 * relation is read over the rows that compute, so the arm's addition is no reason to leave a
 * value of the other side unread, over {@code Int} as over {@code Decimal}.
 */
class AnArmOfAChoiceIsReadOverWhatItsOwnRunWorksOutTest {

    private static final String NOT_SHOWN = "not shown to reach every value";

    private static String comparison(String params, String body) {
        Compilation compilation = Compilation.ofSource("""
                module p
                behavior f : (%s) -> Bool
                let f = %s
                """.formatted(params, body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The way to the arm that adds one states a relation between two numbers of the input, so
     *  that what the arm works out is told of the relation and of nothing else. */
    @Test
    void anAdditionOnAnArmLeavesNoValueOfTheOtherSideUnreadOverInt() {
        String human = comparison("h: Int, d: Int, s: Int",
                "(h, d, s) -> (if d >= h then d + 1 else d) >= s");

        assertFalse(human.contains(NOT_SHOWN), human);
    }

    /** Dates are spaced a day apart, so the same arm is read over them as over whole numbers. The
     *  move on the arm is said as a stop of the rule, shown: a run taking the arm at the last day
     *  there is moves past the calendar. */
    @Test
    void anAdditionOnAnArmLeavesNoValueOfTheOtherSideUnreadOverDate() {
        String human = comparison("h: Date, d: Date, s: Date",
                "(h, d, s) -> (if d >= h then Date.addDays(1, d) else d) >= s");

        assertFalse(human.contains(NOT_SHOWN), human);
        assertTrue(human.contains("may stop a run:"), human);
    }

    /**
     * A choice nested in an arm decides its own arms by what it works out, which the fork around it
     * does not tell: {@code d + 1} stops a run at the greatest {@code Int}, whichever arm the inner
     * choice then takes, and the report says so. Where {@code d + 1} is handed to a call on the
     * arm and not compared, the stop is said of the outer comparison, shown on the arm.
     */
    @Test
    void anArmOfAChoiceNestedInAForkIsNotToldByWhatTheForkDecided() {
        String stopped = "every run stops in d + 1 where d is at least 9223372036854775807";

        String byACondition = comparison("h: Int, d: Int, s: Int",
                "(h, d, s) -> (if d >= h then (if d + 1 > h then d else h) else d) >= s");
        assertTrue(byACondition.contains(stopped), byACondition);

        String byAnOperation = comparison("h: Int, d: Int, s: Int",
                "(h, d, s) -> (if d >= h then Int.max(d + 1, h) else d) >= s");
        assertTrue(byAnOperation.contains("may stop a run:"), byAnOperation);
    }

    /** The same where the way is a membership, which states nothing of the numbers. */
    @Test
    void anAdditionOnAnArmPastAMembershipLeavesNoValueUnreadOverInt() {
        String human = comparison("hs: Set<Int>, d: Int, s: Int",
                "(hs, d, s) -> (if Set.contains(d, hs) then d + 1 else d) >= s");

        assertFalse(human.contains(NOT_SHOWN), human);
    }
}
