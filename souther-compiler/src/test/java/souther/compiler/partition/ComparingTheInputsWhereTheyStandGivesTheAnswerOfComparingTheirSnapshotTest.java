package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@link ReadingState#sameInputsNow} answers what {@link ReadingState#sameInputsBut} answers with
 * the inputs taken.
 *
 * <p>The two differ only where the comparison in place stands in for the copy an input is taken
 * as: a collection that is not a list or a set is compared as the list its copy is, a hash or
 * immutable set or map is compared as it is, and any other is compared by its copy. One case for
 * each of those, one for each way the other roles are compared, and each is held to the answer of
 * taking the inputs as well as to the answer it should be.
 */
class ComparingTheInputsWhereTheyStandGivesTheAnswerOfComparingTheirSnapshotTest {

    private static final class AnOwner {
        /** Read by the state through its role. */
        @SuppressWarnings("UnusedVariable")
        Object collection;
        /** Read by the state through its role. */
        @SuppressWarnings("UnusedVariable")
        Object identified;
        /** Read by the state through its role. */
        @SuppressWarnings("UnusedVariable")
        Object present;
        /** Read by the state through its role. */
        @SuppressWarnings("UnusedVariable")
        List<String> written;
        /** Read by the state through its role. */
        @SuppressWarnings("UnusedVariable")
        Object asked;
    }

    private static final Map<String, ReadingRole> ROLES = Map.of(
            "collection", ReadingRole.INPUT,
            "identified", ReadingRole.IDENTITY,
            "present", ReadingRole.FLAG,
            "written", ReadingRole.WRITTEN,
            "asked", ReadingRole.ASKED);

    private final ReadingState state = new ReadingState(AnOwner.class, ROLES);

    private boolean sameNow(AnOwner then, AnOwner now, boolean askedMatters, BitSet unconsulted,
                            BitSet contentAsked) {
        ReadingState.Inputs taken = state.inputsOf(then);
        boolean byTheSnapshot = state.sameInputsBut(taken, state.inputsOf(now), askedMatters,
                unconsulted, contentAsked);
        boolean inPlace = state.sameInputsNow(taken, now, askedMatters, unconsulted, contentAsked);
        assertEquals(byTheSnapshot, inPlace);
        return inPlace;
    }

    private boolean sameNow(AnOwner then, AnOwner now) {
        return sameNow(then, now, false, null, null);
    }

    private static AnOwner holding(Object collection) {
        AnOwner out = new AnOwner();
        out.collection = collection;
        return out;
    }

    private record Pair(Object then, Object now, boolean same) {}

    @Test
    void aCollectionIsTheSameWhereItsCopyIs() {
        IdentityHashMap<String, Integer> twoOfOne = new IdentityHashMap<>();
        twoOfOne.put("x", 1);
        twoOfOne.put("xy".substring(0, 1), 1);
        IdentityHashMap<String, Integer> twoOfOneAgain = new IdentityHashMap<>();
        twoOfOneAgain.put("x", 1);
        twoOfOneAgain.put("xy".substring(0, 1), 1);
        List<Pair> pairs = List.of(
                new Pair(null, null, true),
                new Pair(null, List.of(), false),
                new Pair(new ArrayList<>(List.of("a", "b")), new ArrayDeque<>(List.of("a", "b")),
                        true),
                new Pair(new ArrayList<>(List.of("a", "b")), new ArrayList<>(List.of("b", "a")),
                        false),
                new Pair(new HashSet<>(List.of("a", "b")),
                        new LinkedHashSet<>(List.of("b", "a")), true),
                new Pair(new HashSet<>(List.of("a", "b")), new ArrayList<>(List.of("a", "b")),
                        false),
                new Pair(Set.of(), new HashSet<>(), true),
                new Pair(Set.of(), List.of(), false),
                new Pair(new HashMap<>(Map.of("a", "b")), new HashMap<>(Map.of("a", "c")), false),
                new Pair(new HashMap<>(Map.of("a", "b")), new TreeMap<>(Map.of("a", "b")), true),
                new Pair(new TreeSet<>(List.of("a", "b")), new TreeSet<>(List.of("a", "c")),
                        false),
                new Pair(twoOfOne, twoOfOneAgain, true));
        for (Pair each : pairs) {
            assertEquals(each.same(), sameNow(holding(each.then()), holding(each.now())),
                    () -> each.then() + " then, " + each.now() + " now");
        }
    }

    @Test
    void anIdentityInputIsTheSameOnlyAsTheVeryObject() {
        String one = "xy".substring(0, 1);
        AnOwner then = new AnOwner();
        then.identified = one;
        AnOwner same = new AnOwner();
        same.identified = one;
        AnOwner equal = new AnOwner();
        equal.identified = "x";

        assertEquals(true, sameNow(then, same));
        assertEquals(false, sameNow(then, equal));
    }

    @Test
    void aFlagInputIsTheSameWhereItIsThereOrNotAndNotWhatItIs() {
        AnOwner there = new AnOwner();
        there.present = "a";
        AnOwner another = new AnOwner();
        another.present = "b";

        assertEquals(true, sameNow(there, another));
        assertEquals(false, sameNow(there, new AnOwner()));
    }

    @Test
    void whatAWrittenInputHoldsIsComparedOnlyWhereTheReadingAskedAfterIt() {
        AnOwner then = new AnOwner();
        then.written = new ArrayList<>(List.of("a"));
        AnOwner more = new AnOwner();
        more.written = new ArrayList<>(List.of("a", "b"));
        BitSet asked = new BitSet();
        asked.set(state.placeOfTheInput("written"));

        assertEquals(true, sameNow(then, more, false, null, null));
        assertEquals(false, sameNow(then, more, false, null, asked));
    }

    @Test
    void anInputTheReadingNeverAskedAfterIsNotCompared() {
        AnOwner then = new AnOwner();
        then.present = "a";
        BitSet unconsulted = new BitSet();
        unconsulted.set(state.placeOfTheInput("present"));

        assertEquals(false, sameNow(then, new AnOwner(), false, null, null));
        assertEquals(true, sameNow(then, new AnOwner(), false, unconsulted, null));
    }

    @Test
    void theAggregatesBeingReadAreComparedOnlyWhereTheReadingAskedAfterThem() {
        AnOwner then = new AnOwner();
        then.asked = new ArrayList<>(List.of("a"));
        AnOwner now = new AnOwner();
        now.asked = new ArrayList<>(List.of("b"));

        assertEquals(true, sameNow(then, now, false, null, null));
        assertEquals(false, sameNow(then, now, true, null, null));
    }
}
