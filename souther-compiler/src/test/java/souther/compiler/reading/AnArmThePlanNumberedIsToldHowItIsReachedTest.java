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
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every arm the plan numbered is told how a run gets to it, or what stands in the way of saying.
 *
 * <p>The question a measure hands on. An arm no row goes through is a gap somebody has to fill, and
 * what fills it is a row that arrives there — so what it takes to arrive is the thing to ask, and
 * asking it of the arms is what this reading is for. Asked of the combinations the body settles
 * together instead, a body whose decisions meet nowhere answered that nothing reaches an arm two
 * classes of its own inputs walk straight into (issue #1009).
 *
 * <p>Total, which is the half that keeps it honest. A key that is not there is a reader deciding
 * what an absence means, and the absence used to mean whatever the caller assumed: the generator
 * read it as an arm no combination reaches, which says the body settles something it does not.
 */
class AnArmThePlanNumberedIsToldHowItIsReachedTest {

    /** Two matches, one per input, one nested in the other. Nothing consumes two decided values
     *  into one, so the body has no meeting at all and every arm is still reached by a pair of
     *  classes. */
    private static final String NESTED = """
            module example.min

            data State = Ready | Running | Paused
            data Button = Start | Reset

            behavior press : (state: State, button: Button) -> State

            let press (state, button) =
                match button with
                    | Start ->
                        match state with
                            | Ready -> Running
                            | Running -> Paused
                            | Paused -> Running
                    | Reset ->
                        match state with
                            | Ready -> Ready
                            | Running -> Running
                            | Paused -> Ready
            """;

    /** One position matched twice, so the arms of the inner match are under a way in that settles
     *  the same decision two ways. Two writings of one comparison are two decisions and would not
     *  do it: what a way in contradicts is a case of a position, which is one decision wherever it
     *  is written. */
    private static final String ASKED_TWICE = """
            module example.same

            data State = Ready | Running

            behavior pick : (s: State) -> Int

            let pick (s) =
                match s with
                    | Ready ->
                        match s with
                            | Ready -> 1
                            | Running -> 2
                    | Running -> 3
            """;

    /** A fork inside a block. The block's body runs where something applies it, under whatever it
     *  is applied to, which is no condition on this behavior's inputs. */
    private static final String IN_A_BLOCK = """
            module example.block

            data Flag = On | Off

            behavior mark : (flags: List<Flag>) -> List<Int>

            let mark (flags) =
                List.map(f ->
                    match f with
                        | On -> 1
                        | Off -> 0, flags)
            """;

    /** A fork whose arms answer values, standing where the value it is part of never arrives. */
    private static final String NOTHING_ARRIVES = """
            module example.aborts

            data State = Ready | Running

            data Out = Int
                invariant value >= 0

            behavior rank : (state: State) -> Out
                constructs Out

            let rank (state) =
                Out((match state with
                        | Ready -> 1
                        | Running -> 2) + unreachable "never")
            """;

    /**
     * The arms of the behavior are the keys, all of them and only them.
     *
     * <p>Read off the plan on both sides, which is what makes it an equation about this reading
     * rather than about the plan. A walk that stops early takes arms out of the answer, and this is
     * what says so — including the arms behind a way in nothing states and behind a place no run
     * reaches, where the walk goes on for no reason but this.
     */
    @Test
    void everyArmOfTheBehaviorIsAnswered() {
        for (String source : List.of(NESTED, ASKED_TWICE, IN_A_BLOCK, NOTHING_ARRIVES)) {
            Read read = read(source);
            assertEquals(read.armSites(), read.answer.arms().keySet(),
                    "every arm the plan numbered is answered, and nothing else is: " + source);
        }
    }

    /**
     * An arm the walk does not reach is this reading falling short, and it says so where it happens.
     *
     * <p>The equation above holds because the reading is held to it, and not because a value was
     * put in for the arms it missed. Such a value is one a reader has to act on, and there is
     * nothing to do about it: it is neither a way in, nor a proof that no run arrives, nor one of
     * the things the path language cannot state. Filled in, a walk that stopped early satisfies
     * the equation and says nothing anybody reads.
     */
    @Test
    void anArmTheWalkDoesNotReachIsRefusedRatherThanFilledIn() {
        Read read = read(NESTED);

        // A collector the walk never told anything, over the same plan: every arm of the behavior
        // is one it is short of.
        Arms missed = new Arms(read.plan);

        assertFalse(read.armSites().isEmpty(), "the behavior has arms to be short of");
        assertThrows(IllegalStateException.class, () -> missed.found(read.behavior),
                "an arm the plan numbered and this did not reach is nothing to hand on");
    }

    /**
     * The way into an arm is the decisions that hold on the way, as one conjunction.
     *
     * <p>The two rows issue #1009 is about. Nothing in this body meets, so no combination of it
     * claims either arm — and each is one input pair away, which is what the way in says and a
     * combination could not.
     */
    @Test
    void theWayIntoAnArmIsWhatHoldsOnTheWayThere() {
        Read read = read(NESTED);

        Set<Set<String>> ways = read.answer.arms().values().stream()
                .filter(PathAccess.Ways.class::isInstance)
                .map(PathAccess.Ways.class::cast)
                .filter(each -> each.ways().size() == 1)
                .map(each -> conditionsOf(each.ways().get(0)))
                .collect(Collectors.toSet());

        assertEquals(8, read.answer.arms().size(), "three arms under each of two, and the two");
        assertTrue(read.answer.arms().values().stream().allMatch(PathAccess.Ways.class::isInstance),
                "every arm here is reached: " + read.answer.arms());
        assertTrue(ways.contains(Set.of("button=Reset", "state=Ready")),
                "the arm `Reset` then `Ready` is reached by that pair: " + ways);
        assertTrue(ways.contains(Set.of("button=Reset", "state=Running")),
                "and so is the one beside it: " + ways);
    }

    /**
     * An arm no run reaches says what shows it, and says it as a fact about the model.
     *
     * <p>Not the same news as a way in this reading cannot state. A reader writes the row the second
     * is about by hand; the first has no row to write, and telling them apart is what stops a limit
     * of this compiler from reading as a proof about the body.
     */
    @Test
    void anArmNoRunReachesSaysWhatShowsIt() {
        Read read = read(ASKED_TWICE);

        List<PathAccess> unreachable = read.answer.arms().values().stream()
                .filter(PathAccess.Unreachable.class::isInstance).toList();

        assertEquals(List.of(new PathAccess.Unreachable(
                        PathAccess.Unreachable.Why.CONTRADICTS_WHAT_ALREADY_HELD)),
                unreachable,
                "the inner else is under the comparison settled both ways: " + read.answer.arms());
    }

    /**
     * An arm inside a block is told what is missing rather than that nothing reaches it.
     *
     * <p>A row through it may well exist. What it takes is what the caller applies the block to,
     * which is not this behavior's inputs and is not something this reading states.
     */
    @Test
    void anArmInsideABlockIsToldWhatIsMissing() {
        Read read = read(IN_A_BLOCK);

        assertTrue(!read.answer.arms().isEmpty(), "the block's fork is numbered");
        for (PathAccess each : read.answer.arms().values()) {
            assertEquals(new PathAccess.Unsupported(
                            PathAccess.Unsupported.Why.RUNS_WHERE_SOMETHING_CALLS_IT), each,
                    "the block runs where something calls it: " + read.answer.arms());
        }
    }

    /** An arm of another behavior, or a number no arm carries, is not a key with an empty answer. */
    @Test
    void aNumberThatIsNoArmOfThisBehaviorIsRefused() {
        Read read = read(NESTED);

        assertInstanceOf(PathAccess.Ways.class, read.answer.armAt(read.armSites().iterator().next()));
        assertThrows(IllegalArgumentException.class, () -> read.answer.armAt(-1));
    }

    /** What the conditions of one way say, as the report of a class would spell them. */
    private static Set<String> conditionsOf(WayIn way) {
        return way.conditions().stream().map(Object::toString).collect(Collectors.toSet());
    }

    private record Read(CoverageRead.Read answer, CoverageSites.Plan plan, String behavior) {

        /** The arms of the behavior, by the numbers the plan gave them. */
        Set<Integer> armSites() {
            return plan.arms(behavior).stream().map(CoverageSites.Site::index)
                    .collect(Collectors.toCollection(java.util.LinkedHashSet::new));
        }
    }

    private static Read read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        String behavior = checked.behaviorBodies().keySet().iterator().next();
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        CoverageSites.Plan plan = CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                checked.supplied());
        return new Read(CoverageRead.of(behavior, body, plan, inputs, symbols), plan, behavior);
    }
}
