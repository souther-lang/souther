package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an operator that settles its answer on the left arrives at.
 *
 * <p>{@code &&} never evaluates its right where the left is false, so an expression whose right
 * aborts still arrives at a value on every run that gets the left to false — and reading the operator
 * as strict in both its sides answers that it arrives nowhere, which takes every arm under a fork on
 * it out of what is measured.
 *
 * <p>Which runs those are is what the left comes out as, so this is the reading of what a value comes
 * to as much as it is the reading of whether one arrives. The two halves are held apart here: a way
 * the reading has worked out a value for settles the answer, and a way it has not is not widened into
 * one that does. {@code a.value > 1} has a value behind each of its ways and {@code 1 > 2} has one
 * behind neither, and a rule reading both as coming out two ways would say the second arrives when no
 * run gets past it.
 */
class AnOperatorThatStopsEarlyIsNotStrictInBothItsSidesTest {

    private static final String TYPES = """
            module example.probe

            data Amount = Int
            data Answer = Int

            behavior pick : (a: Amount, flag: Bool) -> Answer
                constructs Answer

            """;

    /**
     * Whether a body forking on {@code condition} arrives at a value.
     *
     * <p>Asked of the body and not of the condition on its own, because that is how every reader asks
     * it: the fork arrives wherever its condition does, and both arms answer.
     */
    private static boolean arrives(String condition) {
        String source = TYPES
                + "let pick (a, flag) = Answer(if " + condition + " then 1 else 2)\n";
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles: " + condition);
        Core body = checked.behaviorBodies().get("pick");
        assertNotNull(body, "the behavior under test has a body");
        return NormalReturn.of(body);
    }

    @Test
    void aLeftThatSettlesTheAnswerLeavesTheRightUnevaluated() {
        assertTrue(arrives("false && unreachable \"never asked\""));
        assertTrue(arrives("true || unreachable \"never asked\""));
    }

    @Test
    void aLeftThatGoesThroughLeavesTheAnswerToTheRight() {
        assertFalse(arrives("true && unreachable \"always reached\""));
        assertFalse(arrives("false || unreachable \"always reached\""));
    }

    @Test
    void aComparisonWithAValueBehindEachOfItsWaysSettlesTheAnswerOnOneOfThem() {
        assertTrue(arrives("a.value > 1 && unreachable \"no large a reaches here\""));
        assertTrue(arrives("a.value > 1 || unreachable \"no small a reaches here\""));
    }

    /**
     * A comparison the reading cannot value is not one that comes out both ways.
     *
     * <p>The two are one answer apart and the difference is the whole of the direction this reading
     * takes. Nothing stands behind either way of {@code 1 > 2} — the reading does not work out which
     * way it comes out, and it does not read that as coming out both — so the way that would settle
     * the answer on the left is not there and the right is what the expression arrives by.
     */
    @Test
    void aWayNothingStandsBehindDoesNotSettleTheAnswer() {
        assertFalse(arrives("1 > 2 || unreachable \"always reached\""));
        assertFalse(arrives("1 > 2 && unreachable \"under-read\""));
    }

    /**
     * A comparison of a position against itself comes out one way, and nothing here says which.
     *
     * <p>The tripwire for a rule about the shape of the node. Read as a comparison and therefore as
     * coming out both ways, {@code a.value == a.value} would offer a way to false that no run takes,
     * and the expression would be answered as arriving on runs it aborts on.
     */
    @Test
    void aPositionComparedAgainstItselfStandsBehindNeitherWay() {
        assertFalse(arrives("a.value == a.value && unreachable \"always reached\""));
        assertFalse(arrives("a.value /= a.value || unreachable \"always reached\""));
    }

    /**
     * A position holding a truth comes out both ways, and is not a comparison.
     *
     * <p>What stands behind a way is a value of what the expression is over, and that is not a
     * question about which node kind is written. A rule asked only of comparisons would answer that
     * {@code flag && abort} arrives nowhere, when every run with a false {@code flag} arrives — the
     * same failure the operator itself had, one shape along.
     */
    @Test
    void aPositionHoldingATruthComesOutBothWays() {
        assertTrue(arrives("flag && unreachable \"no true flag reaches here\""));
        assertTrue(arrives("flag || unreachable \"no false flag reaches here\""));
    }

    /**
     * A way is witnessed against the range of what is compared, so a number at the end of one closes
     * the way past it.
     *
     * <p>Read off the ends and not by trying values. Nothing whole is greater than the largest whole
     * number, so the only way {@code a.value > that} comes out is false — which settles {@code &&} on
     * the left and sends {@code ||} on to a right no run gets past. Every whole number is at most it,
     * so {@code a.value <= that} comes out true only, and the two operators swap.
     */
    @Test
    void aNumberAtTheEndOfTheRangeClosesTheWayPastIt() {
        assertTrue(arrives("a.value > 9223372036854775807 && unreachable \"never reached\""));
        assertFalse(arrives("a.value > 9223372036854775807 || unreachable \"always reached\""));
        assertTrue(arrives("a.value <= 9223372036854775807 || unreachable \"never reached\""));
        assertFalse(arrives("a.value <= 9223372036854775807 && unreachable \"always reached\""));
    }
}
