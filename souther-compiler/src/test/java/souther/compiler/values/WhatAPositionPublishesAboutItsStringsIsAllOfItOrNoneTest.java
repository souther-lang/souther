package souther.compiler.values;

import org.junit.jupiter.api.Test;

import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.PatternRead;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a position hands to readers that build nothing is every one of its plans or none of them.
 *
 * <p>The rules about the strings at a position are turned into the sets they name so that a reader
 * downstream can draw lines off them, and they are turned into sets out of what that position is
 * allowed. So which of them can be made is not a question about any one of them: a cheap rule
 * beside an expensive one is affordable and is published or not according to what the group came
 * to.
 *
 * <p>Asked one at a time, the answer would have been the ones the allowance reached — a set of
 * rules chosen by the order the building took, published as what the model says. That is the shape
 * this refuses, and it refuses it by there being no way to ask for one.
 */
class WhatAPositionPublishesAboutItsStringsIsAllOfItOrNoneTest {

    /**
     * A pattern somebody wrote, with a place of its own.
     *
     * <p>One occurrence apiece, because two patterns here are two written things: a machine refused
     * for either is answered for by the one that asked, and a place shared between them would be a
     * refusal reported at both.
     */
    private static AdmittedPlan matching(String regex) {
        PatternRead said = PatternParser.read(regex);
        return new AdmittedPlan.Pattern(AuthoredOccurrence.another(), PatternPlan.of(
                assertInstanceOf(PatternRead.Read.class, said).syntax()));
    }

    /** One string, and a machine of some hundreds of states. */
    private static final AdmittedPlan CHEAP = matching("x");
    private static final AdmittedPlan DEAR = matching("a{300}");

    /** Room for the cheap one and not for both. */
    private static Allowance<String> allowing(int states) {
        return Allowance.of(budget(states));
    }

    private static PatternPlan.Budget budget(int states) {
        return new PatternPlan.Budget(states, states);
    }

    @Test
    void everyPlanIsBuiltOrNoneOfThemIs() {
        Realizations made = allowing(50_000).realizeAll("here", List.of(CHEAP, DEAR));

        Realizations.Exact exact = assertInstanceOf(Realizations.Exact.class, made);
        assertNotNull(exact.of(CHEAP), "the cheap rule's strings");
        assertNotNull(exact.of(DEAR), "and the dear one's, out of the same allowance");
    }

    /**
     * And where the allowance does not reach the whole group, the cheap one is not published either.
     *
     * <p>What is asked is the answer and not the spending. The cheap plan is affordable at that
     * size and is built on the way — what it may not do is come out as what the position says while
     * the rule beside it says nothing.
     */
    @Test
    void aGroupTheAllowanceDoesNotReachPublishesNothing() {
        // The size is one the cheap rule fits in and the pair does not, which is the whole of what
        // is being asked. Without this, an allowance too small for either would pass the same
        // assertion and say nothing about a group.
        assertInstanceOf(Realizations.Exact.class,
                allowing(20).realizeAll("here", List.of(CHEAP)),
                "the cheap rule is one this allowance can build");

        Realizations made = allowing(20).realizeAll("here", List.of(CHEAP, DEAR));

        assertInstanceOf(Realizations.NotBuilt.class, made,
                "a rule that was not built takes the ones beside it with it");
    }

    /**
     * The same answer whichever way the caller happened to hold them.
     *
     * <p>And the same spending, which is the half that is not free: what a group costs is settled
     * by working the small ones out first ({@code PlanOrder}), so a walk that met the dear rule
     * first pays what a walk that met the cheap one first pays.
     */
    @Test
    void neitherTheAnswerNorTheSpendingFollowsTheOrderTheyWereGatheredIn() {
        Allowance<String> one = allowing(50_000);
        Allowance<String> other = allowing(50_000);

        Realizations first = one.realizeAll("here", List.of(CHEAP, DEAR));
        Realizations second = other.realizeAll("here", List.of(DEAR, CHEAP));

        assertEquals(assertInstanceOf(Realizations.Exact.class, first).of(DEAR),
                assertInstanceOf(Realizations.Exact.class, second).of(DEAR),
                "the same rules leave the same strings");
        assertEquals(one.left("here"), other.left("here"),
                "and cost the same, however the caller held them");
    }

    /**
     * A machine another question of the position made is used and not made again, wherever it comes
     * up.
     *
     * <p>The parts of a plan are asked for the same way the plan is, so a part somebody else built
     * is found the same way. Looked up only for what a caller named, the two patterns below would
     * be made again underneath the meet — and an allowance meant for the meet alone would be spent
     * on machines that already exist and refuse the very thing it was granted for.
     */
    @Test
    void whatAnotherQuestionBuiltIsUsedInsideAPlanBuiltOutOfIt() {
        AdmittedPlan both = AdmittedPlan.meeting(List.of(CHEAP, DEAR));
        Allowance<String> answers = allowing(50_000);
        assertInstanceOf(Realizations.Exact.class, answers.realizeAll("here", List.of(CHEAP, DEAR)),
                "the two patterns are what the other question built");

        Allowance<String> borrowing = Allowance.besides(budget(50_000), answers);
        Allowance<String> alone = allowing(50_000);
        assertInstanceOf(Realizations.Exact.class,
                borrowing.realizeAll("here", List.of(CHEAP, DEAR, both)));
        assertInstanceOf(Realizations.Exact.class,
                alone.realizeAll("here", List.of(CHEAP, DEAR, both)));

        // The two patterns and everything the meet made of them, against the meet alone. What the
        // difference is worth is the two machines that already existed, which is what a caller
        // asking for a plan built out of them would otherwise pay for a second time.
        assertTrue(spent(borrowing) < spent(alone),
                "a machine another question made is used and not made again: " + spent(borrowing)
                        + " states against " + spent(alone));
    }

    private static int spent(Allowance<String> allowance) {
        return 50_000 - allowance.left("here");
    }

    /**
     * A caller may read an answer for a plan it asked about, and no other.
     *
     * <p>A plan nobody asked to be built has no answer here, and the two lists coming apart is
     * this compiler's mistake rather than a set to hand on. Answered with nothing, it would be
     * published as a rule about which nothing is known.
     */
    @Test
    void anAnswerIsOnlyReadableForAPlanThatWasAskedFor() {
        Realizations made = allowing(50_000).realizeAll("here", List.of(CHEAP));

        assertThrows(IllegalArgumentException.class,
                () -> assertInstanceOf(Realizations.Exact.class, made).of(DEAR));
    }
}
