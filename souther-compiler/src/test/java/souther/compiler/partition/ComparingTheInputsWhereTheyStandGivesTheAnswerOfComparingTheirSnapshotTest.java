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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link ReadingState#sameInputsNow} answers what {@link ReadingState#sameInputsBut} answers
 * with the inputs taken, for every state the inputs are in and every way of asking.
 *
 * <p>A collection that is not a list or a set is compared as the list its copy is, and a set or a
 * map that decides what is in it by another rule than a hash one is compared by its copy, so that
 * leaving out the copy is no change of what is the same.
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

    private static List<Object> collections() {
        List<Object> out = new ArrayList<>();
        out.add(null);
        out.add(List.of());
        out.add(Set.of());
        out.add(Map.of());
        out.add(new ArrayList<>(List.of("a", "b")));
        out.add(new ArrayList<>(List.of("b", "a")));
        out.add(new ArrayDeque<>(List.of("a", "b")));
        out.add(new HashSet<>(List.of("a", "b")));
        out.add(new LinkedHashSet<>(List.of("b", "a")));
        out.add(new TreeSet<>(List.of("a", "b")));
        out.add(new HashMap<>(Map.of("a", "b")));
        out.add(new TreeMap<>(Map.of("a", "b")));
        out.add(new HashMap<>(Map.of("a", "c")));
        IdentityHashMap<String, String> byIdentity = new IdentityHashMap<>();
        byIdentity.put("a", "b");
        out.add(byIdentity);
        out.add("a string");
        out.add(7);
        return out;
    }

    private static List<BitSet> masks() {
        List<BitSet> out = new ArrayList<>();
        out.add(null);
        for (int bits = 0; bits < 16; bits++) {
            BitSet each = new BitSet();
            for (int at = 0; at < 4; at++) {
                each.set(at, (bits & (1 << at)) != 0);
            }
            out.add(each);
        }
        return out;
    }

    private AnOwner owner(Object collection, Object identified, boolean present,
                          List<String> written, Object asked) {
        AnOwner out = new AnOwner();
        out.collection = collection;
        out.identified = identified;
        out.present = present ? "there" : null;
        out.written = written;
        out.asked = asked;
        return out;
    }

    @Test
    void everyPairOfStatesIsToldApartAsItIsByTheirSnapshots() {
        List<Object> collections = collections();
        List<Object> identities = List.of("x", "xy".substring(0, 1));
        List<List<String>> writtens = new ArrayList<>();
        writtens.add(null);
        writtens.add(new ArrayList<>(List.of("a")));
        writtens.add(new ArrayList<>(List.of("a", "b")));
        List<BitSet> masks = masks();
        int compared = 0;
        for (Object thenCollection : collections) {
            for (Object nowCollection : collections) {
                for (Object thenIdentity : identities) {
                    for (Object nowIdentity : identities) {
                        for (List<String> thenWritten : writtens) {
                            for (List<String> nowWritten : writtens) {
                                AnOwner then = owner(thenCollection, thenIdentity, true,
                                        thenWritten, collections.get(4));
                                AnOwner now = owner(nowCollection, nowIdentity,
                                        nowWritten != null, nowWritten, collections.get(5));
                                ReadingState.Inputs taken = state.inputsOf(then);
                                for (BitSet unconsulted : masks) {
                                    for (BitSet contentAsked : masks.subList(0, 4)) {
                                        for (boolean askedMatters : new boolean[] {false, true}) {
                                            assertEquals(
                                                    state.sameInputsBut(taken, state.inputsOf(now),
                                                            askedMatters, unconsulted,
                                                            contentAsked),
                                                    state.sameInputsNow(taken, now, askedMatters,
                                                            unconsulted, contentAsked),
                                                    () -> "then " + thenCollection + ", now "
                                                            + nowCollection + ", identity "
                                                            + thenIdentity + "/" + nowIdentity);
                                            compared++;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        assertTrue(compared > 0);
    }
}
