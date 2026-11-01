package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
        /** Read by the state through its role, and by nothing here but a test that sets it. */
        @SuppressWarnings("UnusedVariable")
        Object holdsOne;
        final List<String> aggregates = new ArrayList<>();
        final List<String> added = new ArrayList<>();
        final Deque<ACandidate> trials = new ArrayDeque<>();
        /** Read by nothing: a field whose role is to be left out of the state. */
        @SuppressWarnings("UnusedVariable")
        long budget = 10;
        /** Read by nothing: a field whose role is to be left out of the state. */
        @SuppressWarnings("UnusedVariable")
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

    /** What a candidate has been told, as it holds it: by relation, with a list under each. */
    private static final class ATeller implements ReadingState.Marked {
        final Map<String, Object> told = new HashMap<>();
        final Map<String, List<Object>> toldOn = new HashMap<>();
        final Map<String, Set<Object>> toldAt = new HashMap<>();
        /** Never named by anything that says what has been told. */
        private final List<Object> forgotten = new ArrayList<>();

        @Override
        public Object mark() {
            return ReadingState.snapshotOfFields(this);
        }
    }

    @Test
    void anObjectPutInPlaceOfAnotherUnderTheSameKeyIsAChange() {
        ATeller teller = new ATeller();
        teller.told.put("relation", new Object());
        Object before = teller.mark();

        teller.told.put("relation", new Object());

        assertFalse(before.equals(teller.mark()), "the map has as many entries as it had");
    }

    @Test
    void somethingAddedToAListHeldUnderAKeyIsAChange() {
        ATeller teller = new ATeller();
        teller.toldOn.put("node", new ArrayList<>());
        Object before = teller.mark();

        teller.toldOn.get("node").add(new Object());

        assertFalse(before.equals(teller.mark()), "the map has as many entries as it had");
    }

    @Test
    void somethingAddedToASetHeldUnderAKeyIsAChange() {
        ATeller teller = new ATeller();
        teller.toldAt.put("node", new HashSet<>());
        Object before = teller.mark();

        teller.toldAt.get("node").add(new Object());

        assertFalse(before.equals(teller.mark()), "the map has as many entries as it had");
    }

    @Test
    void everyFieldIsLookedAtAndNotTheOnesSomebodyNamed() {
        ATeller teller = new ATeller();
        Object before = teller.mark();

        teller.forgotten.add(new Object());

        assertFalse(before.equals(teller.mark()));
    }

    @Test
    void aCollectionThatHoldsItselfIsLookedIntoOnceAndNothingStopsShortOfTheBottom() {
        List<Object> deepest = new ArrayList<>();
        Object nested = deepest;
        for (int level = 0; level < 20; level++) {
            List<Object> around = new ArrayList<>();
            around.add(nested);
            nested = around;
        }
        Object before = ReadingState.snapshotOf(nested);

        deepest.add(new Object());

        assertFalse(before.equals(ReadingState.snapshotOf(nested)),
                "twenty levels down is as much a change as the first");

        List<Object> holdsItself = new ArrayList<>();
        holdsItself.add(holdsItself);
        assertEquals(ReadingState.snapshotOf(holdsItself), ReadingState.snapshotOf(holdsItself));
    }

    @Test
    void theSameThingsHeldInAnotherOrderAreTheSame() {
        Object one = new Object();
        Object other = new Object();
        ATeller first = new ATeller();
        first.toldAt.put("node", new HashSet<>(List.of(one, other)));
        first.toldOn.put("node", new ArrayList<>(List.of(one)));
        ATeller second = new ATeller();
        second.toldAt.put("node", new HashSet<>(List.of(other, one)));
        second.toldOn.put("node", new ArrayList<>(List.of(one)));

        assertEquals(first.mark(), second.mark());
    }

    @Test
    void whatAGuardedMapHoldsUnderAKeyIsWatchedAndNotOnlyHowManyKeysThereAre() {
        class AnotherOwner {
            final Map<String, List<String>> counts = new HashMap<>();
        }
        ReadingState watching = new ReadingState(AnotherOwner.class,
                Map.of("counts", ReadingRole.GUARDED));
        AnotherOwner owner = new AnotherOwner();
        owner.counts.put("count", new ArrayList<>());
        List<Object[]> before = watching.guardsOf(owner);

        owner.counts.get("count").add("a place it was met");

        assertFalse(watching.sameGuards(before, watching.guardsOf(owner)));
    }

    /** An object that gathers what it reaches, in place, while a search is read. */
    private static final class AGatherer {
        final Set<String> through = new HashSet<>();
    }

    /** Searches in progress, each held under the call it answers, as the reader holds them. */
    private static final class AnOwnerOfSearches {
        final IdentityHashMap<Object, AGatherer> searching = new IdentityHashMap<>();
    }

    @Test
    void aFieldHeldByIdentityCannotBeComparedOrLeftAloneForItsValuesChangeInside() {
        for (ReadingRole role : List.of(ReadingRole.INPUT, ReadingRole.IDENTITY,
                ReadingRole.GUARDED, ReadingRole.WRITTEN, ReadingRole.ASKED, ReadingRole.FLAG)) {
            IllegalStateException refused = assertThrows(IllegalStateException.class,
                    () -> new ReadingState(AnOwnerOfSearches.class, Map.of("searching", role)),
                    role.name());

            assertTrue(refused.getMessage().contains("held by identity"), refused.getMessage());
        }
    }

    @Test
    void aSearchInProgressIsNoPlaceToKeepOrTakeAReadingAndAnEmptyOneIs() {
        ReadingState watching = new ReadingState(AnOwnerOfSearches.class,
                Map.of("searching", ReadingRole.ABSENT));
        AnOwnerOfSearches owner = new AnOwnerOfSearches();
        assertTrue(watching.holdsNothing(owner));

        AGatherer gatherer = new AGatherer();
        owner.searching.put(new Object(), gatherer);
        assertFalse(watching.holdsNothing(owner));

        gatherer.through.add("a field it went below");
        owner.searching.clear();
        assertTrue(watching.holdsNothing(owner));
    }

    /** The case the reader is reading, which it looks up by the very node. */
    private record ACase(String name) {}

    @Test
    void anInputHeldByIdentityIsTheSameOnlyForTheSameObject() {
        class AnOwnerOfACase {
            /** Read by the state through its role, and by nothing here but a test that sets it. */
            @SuppressWarnings("UnusedVariable")
            ACase reading = new ACase("when");
        }
        ReadingState watching = new ReadingState(AnOwnerOfACase.class,
                Map.of("reading", ReadingRole.IDENTITY));
        AnOwnerOfACase owner = new AnOwnerOfACase();
        ReadingState.Inputs before = watching.inputsOf(owner);

        assertTrue(watching.sameInputs(before, watching.inputsOf(owner), false));

        owner.reading = new ACase("when");

        assertFalse(watching.sameInputs(before, watching.inputsOf(owner), false),
                "equal as values, and not the object the reading looked up");
    }

    /** What a record of the aggregates in the way being read is, equal to another of its kind. */
    private record AnAggregate(String call, int form) {}

    @Test
    void theAggregatesBeingReadAreTheSameOnlyWhereTheyAreTheVeryOnes() {
        class AnOwnerOfAggregates {
            final List<AnAggregate> aggregates = new ArrayList<>();
        }
        ReadingState watching = new ReadingState(AnOwnerOfAggregates.class,
                Map.of("aggregates", ReadingRole.ASKED));
        AnOwnerOfAggregates owner = new AnOwnerOfAggregates();
        owner.aggregates.add(new AnAggregate("List.length(payable)", 1));
        ReadingState.Inputs before = watching.inputsOf(owner);

        owner.aggregates.clear();
        owner.aggregates.add(new AnAggregate("List.length(payable)", 1));

        assertFalse(watching.sameInputs(before, watching.inputsOf(owner), true),
                "equal as values, and not the aggregate the reading asked after");
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
