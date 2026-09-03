package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number addresses the family it was issued to, and asking it as the other one is refused.
 *
 * <p>Both families take their numbers from one counter, because what records a run is one set of
 * numbers: a number written for an arm and a number written for a comparison are told apart by
 * nothing in the number. So which one a number was issued to is the numbering's answer, given once
 * where the number was handed out — and read back as the other family it would be an address of a
 * place the emitter never lights, which no count can tell from a real one.
 *
 * <p>Held here rather than left to the readers. {@link SiteNumbering#align} asks the family before
 * it reads a number back, so nothing a run produces reaches this; what does reach it is every other
 * caller that has a number and wants a place, and the answer has to be the same for all of them.
 *
 * <p>And a number the numbering never handed out at all, which is the same mistake with nothing to
 * be confused about.
 */
class ANumberMeansTheFamilyItWasIssuedToTest {

    /** An arm at 0 and a comparison at 1, so each family has a number the other does not. */
    private static SiteNumbering numbering() {
        return Numberings.of(Numberings.Family.ARM, Numberings.Family.COMPARISON);
    }

    @Test
    void aComparisonsNumberIsNoArm() {
        IllegalArgumentException refused =
                assertThrows(IllegalArgumentException.class, () -> numbering().arm(1));

        assertTrue(refused.getMessage().contains("which is not an arm"), refused.getMessage());
    }

    @Test
    void anArmsNumberIsNoComparison() {
        IllegalArgumentException refused =
                assertThrows(IllegalArgumentException.class, () -> numbering().comparison(0));

        assertTrue(refused.getMessage().contains("which is not a comparison"),
                refused.getMessage());
    }

    /** And each family reads its own number back, which is what says the refusals above are about
     *  the family and not about reading a number back at all. */
    @Test
    void andEachFamilyReadsItsOwnNumberBack() {
        assertEquals(0, numbering().arm(0).raw());
        assertEquals(1, numbering().comparison(1).raw());
    }

    @Test
    void aNumberThisNumberingNeverHandedOutIsNoPlaceOfIt() {
        assertThrows(IllegalArgumentException.class, () -> numbering().arm(2));
        assertThrows(IllegalArgumentException.class, () -> numbering().comparison(2));
    }
}
