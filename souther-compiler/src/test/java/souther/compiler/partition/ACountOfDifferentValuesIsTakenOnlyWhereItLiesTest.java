package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a count of different values is shown to take is held to what it lies in, and an end is an
 * end: nothing stands for no end by a number. Asked of the arithmetic alone, over every way the
 * values the place takes, how many elements the container holds and what is asked of an element can
 * be, so that what the relation is handed is sound however the pieces come out.
 */
class ACountOfDifferentValuesIsTakenOnlyWhereItLiesTest {

    private static Endpoint at(long count) {
        return Endpoint.inclusive(Count.of(count));
    }

    private static NumericDomain.Bounds between(Long least, Long most) {
        return new NumericDomain.Bounds(least == null ? null : at(least),
                most == null ? null : at(most));
    }

    /** The most elements a container is built of below, and so the most different values. */
    private static final int MOST = 4;

    /**
     * Every count of different values among the elements the statement keeps that a container of
     * between {@code least} and {@code most} elements holds, where the place has {@code values}
     * different ones, each taken by an element that is kept and — where {@code someFail} — one more
     * element the statement fails of: a list may hold an element over again, a set holds each once.
     * The containers are listed whole, so what is reachable is read off them and off no claim.
     */
    private static Set<Integer> reachable(int values, int least, int most, boolean overAgain,
                                          boolean someFail) {
        int kinds = values + (someFail ? 1 : 0);
        Set<Integer> out = new TreeSet<>();
        for (int size = least; size <= Math.min(most, MOST); size++) {
            fill(new int[kinds], 0, size, overAgain, values, out);
        }
        return out;
    }

    /** Adds to {@code out} the count of different kept values of each way of putting {@code left}
     *  more elements among the kinds from {@code from} on, kept ones first. */
    private static void fill(int[] held, int from, int left, boolean overAgain, int values,
                             Set<Integer> out) {
        if (from == held.length) {
            if (left == 0) {
                int different = 0;
                for (int kind = 0; kind < values; kind++) {
                    different += held[kind] > 0 ? 1 : 0;
                }
                out.add(different);
            }
            return;
        }
        for (int each = 0; each <= (overAgain ? left : Math.min(1, left)); each++) {
            held[from] = each;
            fill(held, from + 1, left - each, overAgain, values, out);
        }
        held[from] = 0;
    }

    private static final List<Long> VALUES = Arrays.asList(null, 0L, 1L, 2L, 3L);

    private static final List<Long> MOSTS = Arrays.asList(null, 0L, 1L, 2L, 3L);

    /**
     * What a count is shown to take is a count some container holds, and what a count may be is
     * lied in: asked of every way the number of values the place has, the number of elements a
     * container may hold, whether it may hold one over again and what is asked of an element can
     * be, against the containers listed whole. Where the values counted are not all of them, there
     * may be more than are shown, and what a container may hold is the same however many.
     */
    @Test
    void whatACountIsShownToTakeIsOneSomeContainerHoldsAndLiesWhereItMayBe() {
        List<String> wrong = new ArrayList<>();
        for (Long values : VALUES) {
            for (int least = 0; least <= 2; least++) {
                for (Long most : MOSTS) {
                    if (most != null && most < least) {
                        continue;
                    }
                    for (int flags = 0; flags < 16; flags++) {
                        boolean overAgain = (flags & 1) != 0;
                        boolean everyElement = (flags & 2) != 0;
                        boolean someFail = (flags & 4) != 0;
                        boolean allValues = (flags & 8) != 0;
                        if (everyElement && someFail) {
                            continue;
                        }
                        UndividedByARelation.CountTakes taken = UndividedByARelation.differentTakes(
                                values == null ? null : at(values), allValues,
                                between((long) least, most), between((long) least, most),
                                overAgain, everyElement, someFail);
                        int upTo = most == null ? MOST : (int) Math.min(most, MOST);
                        // What a container may hold: as many values as there may be, and an
                        // element the statement fails of wherever it is not said to keep every one.
                        Set<Integer> possible = reachable(values == null || !allValues ? MOST
                                : (int) (long) values, least, upTo, overAgain, !everyElement);
                        // What the rows show: as many values as are shown to be there, and an
                        // element the statement fails of only where one was found.
                        Set<Integer> shown = reachable(values == null ? MOST : (int) (long) values,
                                least, upTo, overAgain, someFail);
                        if (taken == null) {
                            continue;
                        }
                        for (int count = 0; count <= MOST; count++) {
                            String at = values + "/" + least + ".." + most + "/" + flags + " at "
                                    + count;
                            if (contains(taken.takes(), count) && !shown.contains(count)) {
                                wrong.add("takes a count no container holds: " + at);
                            }
                            if (possible.contains(count) && !contains(taken.lies(), count)) {
                                wrong.add("lies short of a count a container holds: " + at);
                            }
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
    }

    /** Whether {@code count} is in {@code bounds}, an absent end being no end. */
    private static boolean contains(NumericDomain.Bounds bounds, int count) {
        return (bounds.min() == null || bounds.min().at().compareTo(at(count).at()) <= 0)
                && (bounds.max() == null || bounds.max().at().compareTo(at(count).at()) >= 0);
    }

    /**
     * A container held to as many elements as a number can be written as is held to that many. The
     * end the rules leave it is not read as none, though a bare number is what a reader asks it by.
     */
    @Test
    void aBoundAtTheGreatestWholeNumberIsABoundAndNotNone() {
        UndividedByARelation.CountTakes taken = UndividedByARelation.differentTakes(null, false,
                between(0L, null), between(0L, (long) Integer.MAX_VALUE), true, true, false);
        assertNotNull(taken);
        assertEquals(at(Integer.MAX_VALUE), taken.takes().max());

        UndividedByARelation.CountTakes none = UndividedByARelation.differentTakes(null, false,
                between(0L, null), between(0L, null), true, true, false);
        assertNotNull(none);
        assertNull(none.takes().max(), "a container held to no most holds as many as it likes");
    }

    /** What fewer values than elements the place takes is the most, and a container that must hold
     *  more than that many is shown at no value at all. */
    @Test
    void whatThePlaceTakesIsTheMostAndAContainerThatMustHoldMoreIsShownAtNone() {
        UndividedByARelation.CountTakes few = UndividedByARelation.differentTakes(at(2), false,
                between(0L, null), between(0L, null), true, true, false);
        assertNotNull(few);
        assertEquals(at(2), few.takes().max());

        assertNull(UndividedByARelation.differentTakes(at(2), false, between(3L, null),
                between(3L, null), false, true, false));
    }

    /**
     * Where the values the place has are all of them, no count lies past how many there are: a
     * container of any size holds at most that many different values, and is read against a number
     * as far as it reaches. Where what was counted is no more than what was shown, the count lies
     * as far as the container does.
     */
    @Test
    void whereTheValuesCountedAreAllOfThemTheCountLiesNoFurtherThanTheyGo() {
        UndividedByARelation.CountTakes all = UndividedByARelation.differentTakes(at(2), true,
                between(0L, null), between(0L, null), true, true, false);
        assertNotNull(all);
        assertEquals(at(2), all.lies().max());
        assertEquals(at(2), all.takes().max());

        UndividedByARelation.CountTakes shown = UndividedByARelation.differentTakes(at(2), false,
                between(0L, null), between(0L, null), true, true, false);
        assertNotNull(shown);
        assertNull(shown.lies().max());
        assertEquals(at(2), shown.takes().max());

        UndividedByARelation.CountTakes capped = UndividedByARelation.differentTakes(at(17576),
                true, between(0L, 300L), between(0L, 300L), true, true, false);
        assertNotNull(capped);
        assertEquals(at(300), capped.lies().max());
        assertEquals(at(300), capped.takes().max(),
                "up to the cap, and not to the figure a listing of the values stops at");
    }

    /**
     * None is taken where the container may hold none, and where a list that must hold elements may
     * hold only ones the statement fails of; a statement that keeps every element leaves one value
     * at least, and a container that holds each once holds as many values as elements.
     */
    @Test
    void theFewestIsNoneOnlyWhereAnEmptyCountIsAWayToBeHeld() {
        NumericDomain.Bounds twoOrMore = between(2L, null);
        assertEquals(at(0), UndividedByARelation.differentTakes(null, false, twoOrMore,
                twoOrMore, true, false, true).takes().min(),
                "a list of elements the statement fails of");
        assertEquals(at(1), UndividedByARelation.differentTakes(null, false, twoOrMore,
                twoOrMore, true, false, false).takes().min(), "no element is shown to fail it");
        assertEquals(at(1), UndividedByARelation.differentTakes(null, false, twoOrMore,
                twoOrMore, true, true, true).takes().min(), "every element is kept");
        assertEquals(at(2), UndividedByARelation.differentTakes(null, false, twoOrMore,
                twoOrMore, false, false, true).takes().min(), "a container that holds each once");
        assertEquals(at(0), UndividedByARelation.differentTakes(null, false, between(0L, null),
                between(0L, null), false, true, false).takes().min());
        assertTrue(UndividedByARelation.differentTakes(null, false, twoOrMore, twoOrMore, true,
                true, false).lies().min().at().compareTo(at(1).at()) == 0,
                "and the count lies from one");
    }
}
