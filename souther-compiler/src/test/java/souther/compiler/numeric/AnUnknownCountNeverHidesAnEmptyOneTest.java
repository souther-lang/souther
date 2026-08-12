package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many values a type has, where one of the numbers is not known.
 *
 * <p>A record is the product of what its fields hold, and a field with no value leaves the record
 * none however wide the field beside it is. Read as "unknown swallows everything", the product of an
 * unknown and a nothing comes back unknown, and a record nobody can build is admitted on the strength
 * of a sibling nothing was proven about.
 *
 * <p>The other direction is the ordinary one: a sum reaches as far as its widest case, so an unknown
 * beside a nothing is unknown there.
 */
class AnUnknownCountNeverHidesAnEmptyOneTest {

    @Test
    void aProductWithNoValueOnOneSideHasNoValue() {
        assertEquals(Cardinality.NO_VALUE, Cardinality.NO_VALUE.times(Cardinality.UNKNOWN));
        assertEquals(Cardinality.NO_VALUE, Cardinality.UNKNOWN.times(Cardinality.NO_VALUE));
        assertEquals(Cardinality.NO_VALUE, Cardinality.NO_VALUE.times(Cardinality.atMost(7)));
    }

    @Test
    void aSumReachesAsFarAsItsWidestCase() {
        assertEquals(Cardinality.UNKNOWN, Cardinality.NO_VALUE.plus(Cardinality.UNKNOWN));
        assertEquals(Cardinality.UNKNOWN, Cardinality.UNKNOWN.plus(Cardinality.atMost(2)));
        assertEquals(Cardinality.atMost(3), Cardinality.atMost(1).plus(Cardinality.atMost(2)));
    }

    @Test
    void aProductOfKnownSidesIsTheirProduct() {
        assertEquals(Cardinality.atMost(6), Cardinality.atMost(2).times(Cardinality.atMost(3)));
        assertEquals(Cardinality.atMost(1), Cardinality.NO_VALUE.plus(Cardinality.atMost(1)));
    }

    /** A number too large to keep is one no comparison needs, so it comes back as no bound at all. */
    @Test
    void anAnswerTooLargeToKeepIsNoBound() {
        assertEquals(Cardinality.UNKNOWN,
                Cardinality.atMost(Long.MAX_VALUE / 2).times(Cardinality.atMost(4)));
        assertEquals(Cardinality.UNKNOWN, Cardinality.atMost(2).toThe(1000));
    }

    /** A list of one element value has one value per admitted length, and a set has one subset. */
    @Test
    void aPowerAndAChooseAreTheOrdinaryOnes() {
        assertEquals(Cardinality.atMost(8), Cardinality.atMost(2).toThe(3));
        assertEquals(Cardinality.atMost(1), Cardinality.atMost(5).toThe(0));
        assertEquals(Cardinality.atMost(10), Cardinality.atMost(5).choose(2));
        assertEquals(Cardinality.NO_VALUE, Cardinality.atMost(1).choose(2));
        assertEquals(Cardinality.UNKNOWN, Cardinality.UNKNOWN.choose(2));
    }

    /**
     * The one question the transfers ask of a finite answer. Asked of an unknown it is no, because
     * what is not known to be small is not known to be too small to fill anything.
     */
    @Test
    void beingNoWiderThanIsAskedOnlyOfAKnownAnswer() {
        assertTrue(Cardinality.atMost(1).noWiderThan(1));
        assertTrue(Cardinality.NO_VALUE.noWiderThan(0));
        assertFalse(Cardinality.atMost(2).noWiderThan(1));
        assertFalse(Cardinality.UNKNOWN.noWiderThan(Long.MAX_VALUE));
    }
}
