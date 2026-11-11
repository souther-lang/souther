package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;

import java.util.ArrayList;
import java.util.List;

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

    private static final List<Long> ENDS = java.util.Arrays.asList(null, 0L, 1L, 2L, 3L,
            (long) Integer.MAX_VALUE);

    /** Whether {@code inner} lies within {@code outer}, an absent end being no end. */
    private static boolean within(NumericDomain.Bounds inner, NumericDomain.Bounds outer) {
        boolean low = outer.min() == null
                || (inner.min() != null && inner.min().at().compareTo(outer.min().at()) >= 0);
        boolean high = outer.max() == null
                || (inner.max() != null && inner.max().at().compareTo(outer.max().at()) <= 0);
        return low && high;
    }

    @Test
    void whatACountIsShownToTakeLiesWhereItLiesWhateverThePiecesAre() {
        List<String> outside = new ArrayList<>();
        for (Long values : ENDS) {
            for (Long mayLeast : ENDS) {
                for (Long mayMost : ENDS) {
                    for (Long heldMost : ENDS) {
                        for (int flags = 0; flags < 8; flags++) {
                            boolean overAgain = (flags & 1) != 0;
                            boolean everyElement = (flags & 2) != 0;
                            boolean someFail = (flags & 4) != 0;
                            UndividedByARelation.CountTakes taken =
                                    UndividedByARelation.differentTakes(
                                            values == null ? null : at(values),
                                            between(mayLeast == null ? 0L : mayLeast, mayMost),
                                            between(0L, heldMost), overAgain, everyElement,
                                            someFail);
                            if (taken != null && taken.takes().holdsAValue()
                                    && !within(taken.takes(), taken.lies())) {
                                outside.add(values + "/" + mayLeast + ".." + mayMost + "/"
                                        + heldMost + "/" + flags + ": " + taken);
                            }
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), outside);
    }

    /**
     * A container held to as many elements as a number can be written as is held to that many. The
     * end the rules leave it is not read as none, though a bare number is what a reader asks it by.
     */
    @Test
    void aBoundAtTheGreatestWholeNumberIsABoundAndNotNone() {
        UndividedByARelation.CountTakes taken = UndividedByARelation.differentTakes(null,
                between(0L, null), between(0L, (long) Integer.MAX_VALUE), true, true, false);
        assertNotNull(taken);
        assertEquals(at(Integer.MAX_VALUE), taken.takes().max());

        UndividedByARelation.CountTakes none = UndividedByARelation.differentTakes(null,
                between(0L, null), between(0L, null), true, true, false);
        assertNotNull(none);
        assertNull(none.takes().max(), "a container held to no most holds as many as it likes");
    }

    /** What fewer values than elements the place takes is the most, and a container that must hold
     *  more than that many is shown at no value at all. */
    @Test
    void whatThePlaceTakesIsTheMostAndAContainerThatMustHoldMoreIsShownAtNone() {
        UndividedByARelation.CountTakes few = UndividedByARelation.differentTakes(at(2),
                between(0L, null), between(0L, null), true, true, false);
        assertNotNull(few);
        assertEquals(at(2), few.takes().max());

        assertNull(UndividedByARelation.differentTakes(at(2), between(3L, null),
                between(3L, null), false, true, false));
    }

    /**
     * None is taken where the container may hold none, and where a list that must hold elements may
     * hold only ones the statement fails of; a statement that keeps every element leaves one value
     * at least, and a container that holds each once holds as many values as elements.
     */
    @Test
    void theFewestIsNoneOnlyWhereAnEmptyCountIsAWayToBeHeld() {
        NumericDomain.Bounds twoOrMore = between(2L, null);
        assertEquals(at(0), UndividedByARelation.differentTakes(null, twoOrMore, twoOrMore, true,
                false, true).takes().min(), "a list of elements the statement fails of");
        assertEquals(at(1), UndividedByARelation.differentTakes(null, twoOrMore, twoOrMore, true,
                false, false).takes().min(), "no element is shown to fail it");
        assertEquals(at(1), UndividedByARelation.differentTakes(null, twoOrMore, twoOrMore, true,
                true, true).takes().min(), "every element is kept");
        assertEquals(at(2), UndividedByARelation.differentTakes(null, twoOrMore, twoOrMore, false,
                false, true).takes().min(), "a container that holds each once");
        assertEquals(at(0), UndividedByARelation.differentTakes(null, between(0L, null),
                between(0L, null), false, true, false).takes().min());
        assertTrue(UndividedByARelation.differentTakes(null, twoOrMore, twoOrMore, true, true,
                false).lies().min().at().compareTo(at(1).at()) == 0, "and the count lies from one");
    }
}
