package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The identity of a line is where it falls and how much of the quantity its rule wrote, and it is
 * asked for wherever two lines are compared. Whether the host has room to write the count at that
 * place out is a fact about the run, so a line whose digits it cannot write is still a line that has
 * an identity, and two spellings of one such line have the same one.
 */
class ALinesIdentityDoesNotDependOnTheHostHavingRoomForItsDigitsTest {

    private static final Carrier DENSE = new Carrier.Dense();

    private static ExactRatio twoTo(long exponent) {
        return new ExactRatio(BigInteger.ONE, BigInteger.ONE, exponent, 0);
    }

    private static CutPosition written(long count, ExactRatio per) {
        return new CutPosition(new Level.OnACarrier(DENSE, Count.of(count)), per);
    }

    /** Two to the two-to-the-fortieth: a whole number, and one no host has room to write out. */
    private static final long FAR = 1L << 40;

    @Test
    void aLineWhoseCountTheHostCannotWriteOutHasAnIdentity() {
        CutPosition far = written(1, twoTo(-FAR));
        assertFalse(Level.OnACarrier.held(DENSE, far.exactly()).isHeld(),
                "the line falls at a count the host cannot write, which is what this asks about");

        CutPosition identity = assertDoesNotThrow(far::canonical);

        assertInstanceOf(Level.OfTheQuantity.class, identity.written(),
                "and the identity is the number itself where there is no count to put it on");
    }

    @Test
    void twoSpellingsOfOneLineThatFarOutAreOneIdentity() {
        CutPosition once = written(2, twoTo(-FAR + 1));
        CutPosition twice = written(1, twoTo(-FAR));

        assertEquals(once.exactly(), twice.exactly(), "the two are written differently");
        assertEquals(once.canonical(), twice.canonical());
    }

    @Test
    void aLineTheHostCanWriteKeepsTheCarrierItWasWrittenOn() {
        CutPosition near = written(4, ExactRatio.of(2));

        assertInstanceOf(Level.OnACarrier.class, near.canonical().written());
    }
}
