package souther.compiler.check;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The arithmetic over counts, and the one answer it cannot arrive at.
 *
 * <p>A count of none is a claim about a type and carries the proof that showed it, so nothing that
 * has no proof to hand may produce one. What the operations here are closed over is
 * {@link Cardinality.Standing} — every sum, product, power and subset count of those is one of them
 * again — which leaves the named readings in {@link CardinalityTransfer} as the whole list of places
 * a type comes to have no value.
 *
 * <p>That a field with no value leaves the record none is still true and is not this arithmetic's
 * doing. It is read off the field before anything is multiplied, which is also what lets the record
 * carry the field's proof.
 *
 * <p>Not knowing a bound is the wide answer. It is not a large number and every question asked of it
 * comes back the way that refuses nothing, so a sum reaching it is unknown and so is a product.
 */
class ACountOfNoneIsNeverReachedByArithmeticTest {

    @Test
    void aSumReachesAsFarAsItsWidestCase() {
        assertEquals(Cardinality.UNKNOWN, Cardinality.UNKNOWN.plus(Cardinality.atMost(2)));
        assertEquals(Cardinality.atMost(3), Cardinality.atMost(1).plus(Cardinality.atMost(2)));
    }

    @Test
    void aProductOfKnownSidesIsTheirProduct() {
        assertEquals(Cardinality.atMost(6), Cardinality.atMost(2).times(Cardinality.atMost(3)));
        assertEquals(Cardinality.UNKNOWN, Cardinality.atMost(2).times(Cardinality.UNKNOWN));
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
        assertEquals(Cardinality.UNKNOWN, Cardinality.UNKNOWN.choose(2));
    }

    /**
     * A subset larger than there are values is not a question this answers.
     *
     * <p>That a set cannot be filled from its element is one comparison of two counts, made where the
     * set is read and carrying the proof of it. Answering it here as well would be the same refusal
     * arrived at a second way, with nothing to say for itself.
     */
    @Test
    void asubsetLargerThanTheValuesThereAreIsRefusedWhereTheSetIsRead() {
        assertThrows(IllegalArgumentException.class, () -> Cardinality.atMost(1).choose(2));
    }

    /** And a count of none is not a number anything writes. */
    @Test
    void aCountOfNoneIsWrittenAsAProof() {
        assertThrows(IllegalArgumentException.class, () -> Cardinality.atMost(0));
        assertThrows(IllegalArgumentException.class, () -> Cardinality.none(null));
        assertTrue(Cardinality.none(new Emptiness.ConflictingRules()).none());
    }

    /** Two readings of one position both hold, so the smaller number is the one true of it. */
    @Test
    void theNarrowerOfTwoBoundsIsTheOneThatHolds() {
        assertEquals(Cardinality.atMost(2),
                Cardinality.Standing.narrower(Cardinality.atMost(2), Cardinality.atMost(5)));
        assertEquals(Cardinality.atMost(2),
                Cardinality.Standing.narrower(Cardinality.UNKNOWN, Cardinality.atMost(2)));
        assertEquals(Cardinality.UNKNOWN,
                Cardinality.Standing.narrower(Cardinality.UNKNOWN, Cardinality.UNKNOWN));
    }

    /**
     * Having no bound is not the largest number, so the largest number is narrower than it.
     *
     * <p>Both ways round, because a reading that stands the unknown in for a number puts the two of
     * them level and then answers with whichever it was handed first.
     */
    @Test
    void aBoundThatWasProvenIsNarrowerThanNoBoundHoweverLargeItIs() {
        assertEquals(Cardinality.atMost(Long.MAX_VALUE), Cardinality.Standing.narrower(
                Cardinality.UNKNOWN, Cardinality.atMost(Long.MAX_VALUE)));
        assertEquals(Cardinality.atMost(Long.MAX_VALUE), Cardinality.Standing.narrower(
                Cardinality.atMost(Long.MAX_VALUE), Cardinality.UNKNOWN));
    }
}
