package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operator that stops as soon as its answer is settled has paths to a value, and they are its
 * outcomes.
 *
 * <p>Not a meeting, which is a different claim and stays. The two sides are not consumed into one
 * value, so nothing asks for the combinations of their decisions; what {@code A && B} has instead
 * is the left settling the answer on its own and the left going through with the right settling
 * it, which is as many paths to a value as the run has and is what a factor is made of.
 *
 * <p>Which of the left's outcomes goes through is which value it comes to, so the reading has to
 * answer what a subexpression evaluates to and not only under what conditions it is reached. Where
 * it cannot say — a call, a plain {@code Bool} the body only reads — the paths are not enumerated
 * at all rather than enumerated in part, because a partial list of the ways in to a value reads as
 * a complete one and would offer a group under a way in a row cannot be steered down.
 *
 * <p>Written without helpers on purpose. What a helper is spliced into a body as is another
 * reading's answer, and a group shape that depended on it would be measuring two things at once.
 */
class AShortCircuitOperatorsPathsToAValueAreItsOutcomesTest {

    /** Three comparisons joined by an operator that stops early, and the fork's value summed. */
    private static final String CHAIN = """
            module example.chain

            behavior fee : (a: Int, b: Int, c: Int, d: Int) -> Int

            let fee (a, b, c, d) =
                (if a > 1 && b > 2 && c > 3 then 1 else 0) + (if d > 4 then 10 else 0)
            """;

    /** A meeting standing in the last operand of a chain, which is reached under the ones before. */
    private static final String IN_THE_RIGHT_OPERAND = """
            module example.right

            behavior pick : (a: Int, b: Int, c: Int, d: Int) -> Int

            let pick (a, b, c, d) =
                if a > 1 && b > 2
                        && ((if c > 3 then 1 else 0) + (if d > 4 then 10 else 0)) > 5
                    then 100
                    else 200
            """;

    /** A meeting in the arm taken when every comparison of the condition held. */
    private static final String IN_THE_ARM_THAT_HOLDS = """
            module example.holds

            behavior fee : (a: Int, b: Int, c: Int, d: Int) -> Int

            let fee (a, b, c, d) =
                if a > 1 && b > 2
                    then (if c > 3 then 1 else 0) + (if d > 4 then 10 else 0)
                    else 0
            """;

    /** The same meeting in the arm the condition fails into, which is reached two ways. */
    private static final String IN_THE_ARM_THAT_FAILS = """
            module example.fails

            behavior fee : (a: Int, b: Int, c: Int, d: Int) -> Int

            let fee (a, b, c, d) =
                if a > 1 && b > 2
                    then 0
                    else (if c > 3 then 1 else 0) + (if d > 4 then 10 else 0)
            """;

    /** The same three comparisons bracketed the other way round. */
    private static final String BRACKETED_RIGHT = """
            module example.bracketed

            behavior fee : (a: Int, b: Int, c: Int, d: Int) -> Int

            let fee (a, b, c, d) =
                (if a > 1 && (b > 2 && c > 3) then 1 else 0) + (if d > 4 then 10 else 0)
            """;

    /** A left side whose value this reading cannot say, standing before one it can. */
    private static final String UNREADABLE_LEFT = """
            module example.unreadableleft

            behavior fee : (p: Bool, a: Int, c: Int, d: Int) -> Int

            let fee (p, a, c, d) =
                if p && a > 1
                    then (if c > 3 then 1 else 0) + (if d > 4 then 10 else 0)
                    else 0
            """;

    /** A right side whose value this reading cannot say, standing after one it can. */
    private static final String UNREADABLE_RIGHT = """
            module example.unreadableright

            behavior fee : (p: Bool, a: Int, c: Int, d: Int) -> Int

            let fee (p, a, c, d) =
                if a > 1 && p
                    then (if c > 3 then 1 else 0) + (if d > 4 then 10 else 0)
                    else 0
            """;

    /** The same chain, given a name before the fork that tests it. */
    private static final String NAMED_BEFORE_THE_FORK = """
            module example.named

            behavior fee : (a: Int, b: Int, c: Int, d: Int) -> Int

            let fee (a, b, c, d) = {
                let ok = a > 1 && b > 2 && c > 3

                (if ok then 1 else 0) + (if d > 4 then 10 else 0)
            }
            """;

    private static List<Interaction> read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return CoverageRead.of(behavior, body,
                CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                checked.supplied()), inputs, symbols).interactions();
    }

    /** The sizes of each group's factors, which is the shape of the space a row is owed for. */
    private static List<List<Integer>> shape(List<Interaction> found) {
        return found.stream()
                .map(group -> group.factors().stream().map(f -> f.outcomes().size()).toList())
                .toList();
    }

    /** What each factor of each group is settled by, as the conditions are written. */
    private static List<List<List<String>>> outcomes(List<Interaction> found) {
        return found.stream()
                .map(group -> group.factors().stream()
                        .map(factor -> factor.outcomes().stream().map(Object::toString).toList())
                        .toList())
                .toList();
    }

    /** What each group's way in is made of, said by the kind of condition each decision is. */
    private static List<List<String>> reachKinds(List<Interaction> found) {
        return found.stream()
                .map(group -> group.reach().stream()
                        .map(decision -> decision.constrains().getClass().getSimpleName())
                        .toList())
                .toList();
    }

    /**
     * Three comparisons that between them settle one value are four paths to it and not one.
     *
     * <p>The left settles the answer at the first comparison that fails, and the value goes
     * through only where every one of them held — so what the fork above answers with varies four
     * ways, which is what the operand of the sum it is written in is a factor of.
     */
    @Test
    void aChainOfComparisonsIsAsManyPathsAsItHasWaysToSettle() {
        assertEquals(List.of(List.of(4, 2)), shape(read(CHAIN, "fee")),
                "the chain settles four ways and the other charge two");
    }

    /**
     * The paths are the same however the chain is bracketed.
     *
     * <p>Which matters because the reading takes one operator at a time and an answer that turned
     * on how the run was written down would be an answer about the writing. A path is the left
     * settling the answer, or the left going through and what follows settling it — and that
     * composes the same whichever end the run is read from.
     */
    @Test
    void howAChainIsBracketedIsNotWhatItsPathsAre() {
        assertEquals(outcomes(read(CHAIN, "fee")), outcomes(read(BRACKETED_RIGHT, "fee")),
                "the same three comparisons settle the same four ways");
    }

    /**
     * The last operand of a chain is reached under the comparisons before it, and a group in there
     * is offered under them.
     *
     * <p>Read as a condition rather than a value, what it takes to get here cannot be said as soon
     * as the left is more than one comparison — and a walk that will not name a way in does not go
     * in at all, so the meeting in here was not found.
     */
    @Test
    void aMeetingInALaterOperandIsReachedUnderTheOnesBeforeIt() {
        List<Interaction> found = read(IN_THE_RIGHT_OPERAND, "pick");

        assertEquals(List.of(List.of(2, 2)), shape(found), "the two charges meet once: " + found);
        assertEquals(List.of(List.of("Side", "Side")), reachKinds(found),
                "under both comparisons of the left having held: " + found);
    }

    /**
     * The arm a condition holds into is reached by every comparison of it coming out that way, and
     * saying so is what places the way in at a class of an input.
     *
     * <p>A fork whose condition is a chain names no comparison, so the arm was all there was to say
     * — and an arm places at nothing, which takes the group with it.
     */
    @Test
    void theArmAConditionHoldsIntoIsReachedByEveryComparisonOfItHolding() {
        List<Interaction> found = read(IN_THE_ARM_THAT_HOLDS, "fee");

        assertEquals(List.of(List.of(2, 2)), shape(found), "the two charges meet once: " + found);
        assertEquals(List.of(List.of("Side", "Side")), reachKinds(found),
                "under both comparisons having held: " + found);
    }

    /**
     * The arm a condition fails into is reached as many ways as the condition has to fail, and the
     * meeting standing in it is offered under each of them.
     *
     * <p>Two paths and not one alternative: a row that made the first comparison fail never
     * evaluated the second, and a row that made the second fail had the first hold. A way in this
     * reading carries is a conjunction, so what is written down is one group per path rather than
     * one group naming both.
     *
     * <p>Ordered by the left, which is the order the paths are read off it: each of the left's own
     * ways is taken in turn and the one that goes through is extended by the right where it stands,
     * so the path that reached the second comparison comes before the one that never got there.
     */
    @Test
    void theArmAConditionFailsIntoIsReachedOncePerWayItFails() {
        List<Interaction> found = read(IN_THE_ARM_THAT_FAILS, "fee");

        assertEquals(List.of(List.of(2, 2), List.of(2, 2)), shape(found),
                "the two charges meet under each way the condition fails: " + found);
        assertEquals(List.of(List.of("Side", "Side"), List.of("Side")), reachKinds(found),
                "the first comparison holding with the second failing, and it failing: " + found);
    }

    /**
     * A side whose value this reading cannot say leaves the paths unenumerated, and what stands
     * after it is read no further.
     *
     * <p>Under-reading is the safe direction and this is where it is taken. The reading knows the
     * value goes through where the left does, and it cannot say when the left does — so it does
     * not know whether the comparison after it was evaluated at all, and a list of the ways the
     * condition holds would be a list with paths missing from it.
     */
    @Test
    void aSideThisReadingCannotValueLeavesThePathsUnenumerated() {
        assertEquals(List.of(List.of("Arm")), reachKinds(read(UNREADABLE_LEFT, "fee")),
                "nothing says when the plain flag lets the comparison be reached");
    }

    /**
     * The same where it is the right that cannot be valued, which the left still divides.
     *
     * <p>The condition fails where the first comparison fails, which is a path this reading has;
     * where it holds, whether the answer went through is the flag's business and unsaid. One of
     * the two paths being known is not the enumeration being known, so neither arm is named by the
     * comparisons.
     */
    @Test
    void oneKnownPathIsNotAnEnumerationOfThem() {
        assertEquals(List.of(List.of("Arm")), reachKinds(read(UNREADABLE_RIGHT, "fee")),
                "the ways the condition holds are not all of them said");
    }

    /**
     * Giving the chain a name before the fork does not change what the chain is read as.
     *
     * <p>Which is the whole of what the naming has to answer for. {@code let ok = …} then
     * {@code if ok} and the chain written in the condition are the same run and the same rules, so
     * a reading that told them apart would be reading where the comparisons stand rather than what
     * they say — and it did, because a comparison was numbered only where a fork was written
     * directly around it.
     *
     * <p>Held as an equality against the inline form and not as a shape of its own. A count that
     * happened to match would say nothing about the decisions being the same ones.
     */
    @Test
    void namingAChainBeforeTheForkIsNotWhatItsPathsAre() {
        assertEquals(outcomes(read(CHAIN, "fee")), outcomes(read(NAMED_BEFORE_THE_FORK, "fee")),
                "the same three comparisons settle the same four ways under either spelling");
    }

    /**
     * A short circuit is still not a meeting of its two sides.
     *
     * <p>What the reading gained is the paths to the operator's value, which is one factor. The
     * combinations of the two sides' decisions are still combinations no path takes, and nothing
     * asks for them.
     */
    @Test
    void anOperatorThatStopsEarlyIsStillNotAMeetingOfItsSides() {
        List<Interaction> found = read(CHAIN, "fee");

        assertTrue(found.stream().allMatch(group -> group.factors().size() == 2),
                "the sum is the only meeting, and it is of two charges: " + found);
    }
}
