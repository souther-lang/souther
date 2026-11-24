package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReadingState.Bindings;
import souther.compiler.partition.ReadingState.Compared;
import souther.compiler.partition.ReadingState.Members;
import souther.compiler.partition.ReadingState.Restore;
import souther.compiler.partition.ReadingState.Scoped;
import souther.compiler.partition.ReadingState.Layers;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a reading depends on and must leave alone is the parts the state is made of, each compared
 * as it was made to be.
 *
 * <p>Asked of a state made for the purpose, so that each kind of part is seen at work on its own
 * and a change to that part is the one thing that differs.
 */
class TheStateOfAReadingIsTakenFromItsPartsTest {

    /** A candidate that says what it has said, as a rule being tried does. */
    private static final class ACandidate implements ReadingState.Marked {
        int said;

        @Override
        public Object mark() {
            return said;
        }
    }

    private final ReadingState state = new ReadingState();
    private final Members<String> scoped = state.members();
    private final Scoped<Object> holdsOne = state.setting(Compared.BY_PRESENCE);
    private final Layers<String> aggregates = state.aggregates();
    private final Layers<ACandidate> trials = state.trials();
    private final Scoped<Object> notCompared = state.notCompared(null);

    @Test
    void aChangeToAnInputIsSeenAndPuttingItBackIsNot() {
        ReadingState.Inputs before = state.inputs();

        try (Restore _ = scoped.adding("quantified")) {
            assertFalse(state.sameInputs(before, state.inputs(), false, 0));
        }
        assertTrue(state.sameInputs(before, state.inputs(), false, 0));
    }

    @Test
    void theInputsAreCopiedSoALaterChangeToTheCollectionIsNotAChangeToThem() {
        ReadingState.Inputs before;
        try (Restore _ = scoped.adding("quantified")) {
            before = state.inputs();
        }

        assertFalse(state.sameInputs(before, state.inputs(), false, 0));
    }

    @Test
    void aPartHeldByPresenceIsWhetherThereIsOneAndNotWhichOneItIs() {
        ReadingState.Inputs before;
        try (Restore _ = holdsOne.set(new Object())) {
            before = state.inputs();
            try (Restore _ = holdsOne.set(new Object())) {
                assertTrue(state.sameInputs(before, state.inputs(), false, 0));
            }
        }

        assertFalse(state.sameInputs(before, state.inputs(), false, 0));
    }

    @Test
    void whatIsAskedAfterIsComparedOnlyForAReadingThatAskedAfterIt() {
        ReadingState.Inputs before = state.inputs();

        try (Restore _ = aggregates.pushing("an aggregate")) {
            assertTrue(state.sameInputs(before, state.inputs(), false, 0));
            assertFalse(state.sameInputs(before, state.inputs(), true, 0));
        }
    }

    /**
     * What readings kept are told apart by before any is compared
     * ({@code SharedReads.Scene#requiredInputsHash}) is the hash of the values, so the values are
     * what every comparison asks: whatever a reading asked after, inputs that differ in their
     * values are not the same, and inputs that differ in what was asked after only have the same
     * values.
     */
    @Test
    void inputsDifferingInTheirValuesAreTheSameForNoReading() {
        ReadingState.Inputs before = state.inputs();

        try (Restore _ = aggregates.pushing("an aggregate")) {
            ReadingState.Inputs asked = state.inputs();
            assertTrue(state.sameInputs(before, asked, false, 0));
            assertEquals(state.requiredInputsHash(before), state.requiredInputsHash(asked));

            try (Restore _ = scoped.adding("quantified")) {
                ReadingState.Inputs other = state.inputs();
                for (boolean askedMatters : new boolean[] {false, true}) {
                    assertFalse(state.sameInputs(before, other, askedMatters, 0));
                }
                assertFalse(state.sameAskedInputsBut(before, other, 0, null));
            }
        }
    }


    @Test
    void theCandidateBeingTriedIsSeenWhenSomethingIsSaidIntoItAndWhenAnotherStandsInItsPlace() {
        try (Restore _ = trials.pushing(new ACandidate())) {
            List<Object[]> before = state.guards();

            trials.newest().said++;
            assertFalse(state.sameGuards(before, state.guards()));

            trials.newest().said--;
            assertTrue(state.sameGuards(before, state.guards()));

            try (Restore _ = trials.pushing(new ACandidate())) {
                assertFalse(state.sameGuards(before, state.guards()));
            }
        }
    }

    @Test
    void whatIsNeitherAnInputNorLeftAloneIsNotLookedAt() {
        ReadingState.Inputs inputs = state.inputs();
        List<Object[]> guards = state.guards();

        try (Restore _ = notCompared.set(new Object())) {
            assertTrue(state.sameInputs(inputs, state.inputs(), true, 0));
            assertTrue(state.sameGuards(guards, state.guards()));
        }
    }

    @Test
    void anInputHeldByIdentityIsTheSameOnlyForTheSameObject() {
        record ACase(String name) {}
        ReadingState watching = new ReadingState();
        Scoped<ACase> reading = watching.setting(Compared.BY_IDENTITY, new ACase("when"));
        ReadingState.Inputs before = watching.inputs();

        assertTrue(watching.sameInputs(before, watching.inputs(), false, 0));

        try (Restore _ = reading.set(new ACase("when"))) {
            assertFalse(watching.sameInputs(before, watching.inputs(), false, 0),
                    "equal as values, and not the object the reading looked up");
        }
    }

    @Test
    void theAggregatesBeingReadAreTheSameOnlyWhereTheyAreTheVeryOnes() {
        record AnAggregate(String call, int form) {}
        ReadingState watching = new ReadingState();
        Layers<AnAggregate> held = watching.aggregates();
        ReadingState.Inputs before;
        try (Restore _ = held.pushing(new AnAggregate("List.length(payable)", 1))) {
            before = watching.inputs();
        }

        try (Restore _ = held.pushing(new AnAggregate("List.length(payable)", 1))) {
            assertFalse(watching.sameInputs(before, watching.inputs(), true, 0),
                    "equal as values, and not the aggregate the reading asked after");
        }
    }

    @Test
    void aSearchInProgressIsNoPlaceToKeepOrTakeAReadingAndAnEmptyOneIs() {
        ReadingState watching = new ReadingState();
        Bindings<Object, Set<String>> searching = watching.searchBindings();
        assertTrue(watching.holdsNothing());

        Set<String> through = new HashSet<>();
        try (Restore _ = searching.binding(new Object(), through)) {
            assertFalse(watching.holdsNothing());
            through.add("a field it went below");
        }

        assertTrue(watching.holdsNothing());
    }

    @Test
    void aValueSetForAnExtentIsPutBackWhenTheExtentEndsByAnException() {
        ReadingState watching = new ReadingState();
        Scoped<String> setting = watching.setting(Compared.BY_VALUE, "outside");

        assertThrows(IllegalStateException.class, () -> setting.during("inside", () -> {
            throw new IllegalStateException("the reading stopped");
        }));

        assertEquals("outside", setting.get());
    }

    @Test
    void aKeyBoundForAnExtentIsBoundAgainToWhatItWasAndNotLeftUnbound() {
        ReadingState watching = new ReadingState();
        Bindings<String, Integer> bound = watching.bindings();

        try (Restore _ = bound.binding("acc", 1)) {
            try (Restore _ = bound.binding("acc", 2)) {
                assertEquals(2, bound.get("acc"));
            }
            assertEquals(1, bound.get("acc"), "the binding around is the one put back");
        }

        assertFalse(bound.containsKey("acc"));
    }

    @Test
    void aMemberAlreadyInIsNoMemberEnteredAgain() {
        ReadingState watching = new ReadingState();
        Members<String> in = watching.members();

        try (Restore _ = in.adding("xs")) {
            assertThrows(IllegalStateException.class, () -> in.adding("xs"),
                    "taking it out at the end of the inner extent would take out the outer one");
        }
    }

    @Test
    void membersEmptiedForAnExtentAreThereAgainAfterIt() {
        ReadingState watching = new ReadingState();
        Members<String> in = watching.members();

        try (Restore _ = in.adding("xs")) {
            try (Restore _ = in.emptied()) {
                assertTrue(in.isEmpty());
            }
            assertTrue(in.contains("xs"));
        }
    }

    @Test
    void whatIsOnTopIsTheNewestAndTheOthersAreUnderItInTheOrderTheyCame() {
        ReadingState watching = new ReadingState();
        Layers<String> stack = watching.stack();

        try (Restore _ = stack.pushing("outer"); Restore _ = stack.pushing("inner")) {
            assertEquals("inner", stack.newest());
            assertEquals(List.of("outer", "inner"), stack.oldestFirst());
            assertEquals(List.of("inner", "outer"), stack.newestFirst());
        }

        assertNull(stack.newest());
    }

}
