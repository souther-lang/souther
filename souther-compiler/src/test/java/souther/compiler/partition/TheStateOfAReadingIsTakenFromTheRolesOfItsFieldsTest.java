package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading depends on and must leave alone is the fields the roles table says so of, and no
 * list written beside it.
 *
 * <p>Asked of an owner made for the purpose, so that each role is seen at work on a field of its
 * own and a change to that field is the one thing that differs.
 */
class TheStateOfAReadingIsTakenFromTheRolesOfItsFieldsTest {

    /** A candidate that says what it has said, as a rule being tried does. */
    private static final class ACandidate implements ReadingState.Marked {
        int said;

        @Override
        public Object mark() {
            return said;
        }
    }

    private static final class AnOwner {
        final Set<String> scoped = new HashSet<>();
        Object holdsOne;
        final List<String> aggregates = new ArrayList<>();
        final List<String> added = new ArrayList<>();
        final Deque<ACandidate> trials = new ArrayDeque<>();
        long budget = 10;
        final String fixed = "same";
    }

    private static final Map<String, ReadingRole> ROLES = Map.of(
            "scoped", ReadingRole.INPUT,
            "holdsOne", ReadingRole.FLAG,
            "aggregates", ReadingRole.ASKED,
            "added", ReadingRole.GUARDED,
            "trials", ReadingRole.TRIAL,
            "budget", ReadingRole.BUDGET,
            "fixed", ReadingRole.FIXED);

    private final ReadingState state = new ReadingState(AnOwner.class, ROLES);
    private final AnOwner owner = new AnOwner();

    @Test
    void aFieldWithNoRoleStopsTheStateWhereItIsMade() {
        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> new ReadingState(AnOwner.class, Map.of("scoped", ReadingRole.INPUT)));

        assertTrue(refused.getMessage().contains("has no role"), refused.getMessage());
    }

    @Test
    void aChangeToAnInputIsSeenAndPuttingItBackIsNot() {
        ReadingState.Inputs before = state.inputsOf(owner);

        owner.scoped.add("quantified");
        assertFalse(state.sameInputs(before, state.inputsOf(owner), false));

        owner.scoped.remove("quantified");
        assertTrue(state.sameInputs(before, state.inputsOf(owner), false));
    }

    @Test
    void theInputsAreCopiedSoALaterChangeToTheCollectionIsNotAChangeToThem() {
        owner.scoped.add("quantified");
        ReadingState.Inputs before = state.inputsOf(owner);

        owner.scoped.clear();

        assertFalse(state.sameInputs(before, state.inputsOf(owner), false));
    }

    @Test
    void aFlagIsWhetherThereIsOneAndNotWhichOneItIs() {
        owner.holdsOne = new Object();
        ReadingState.Inputs before = state.inputsOf(owner);

        owner.holdsOne = new Object();
        assertTrue(state.sameInputs(before, state.inputsOf(owner), false));

        owner.holdsOne = null;
        assertFalse(state.sameInputs(before, state.inputsOf(owner), false));
    }

    @Test
    void whatIsAskedAfterIsComparedOnlyForAReadingThatAskedAfterIt() {
        ReadingState.Inputs before = state.inputsOf(owner);

        owner.aggregates.add("an aggregate");

        assertTrue(state.sameInputs(before, state.inputsOf(owner), false));
        assertFalse(state.sameInputs(before, state.inputsOf(owner), true));
    }

    @Test
    void whatAReadingMustLeaveAloneIsSeenWhenItAddsToIt() {
        List<Object[]> before = state.guardsOf(owner);

        owner.added.add("a part it would not add again");

        assertFalse(state.sameGuards(before, state.guardsOf(owner)));
    }

    @Test
    void theCandidateBeingTriedIsSeenWhenSomethingIsSaidIntoItAndWhenAnotherStandsInItsPlace() {
        owner.trials.push(new ACandidate());
        List<Object[]> before = state.guardsOf(owner);

        owner.trials.peek().said++;
        assertFalse(state.sameGuards(before, state.guardsOf(owner)));

        owner.trials.peek().said--;
        assertTrue(state.sameGuards(before, state.guardsOf(owner)));

        owner.trials.push(new ACandidate());
        assertFalse(state.sameGuards(before, state.guardsOf(owner)));
    }

    @Test
    void whatIsNeitherAnInputNorLeftAloneIsNotLookedAt() {
        ReadingState.Inputs inputs = state.inputsOf(owner);
        List<Object[]> guards = state.guardsOf(owner);

        owner.budget--;

        assertTrue(state.sameInputs(inputs, state.inputsOf(owner), true));
        assertTrue(state.sameGuards(guards, state.guardsOf(owner)));
    }
}
