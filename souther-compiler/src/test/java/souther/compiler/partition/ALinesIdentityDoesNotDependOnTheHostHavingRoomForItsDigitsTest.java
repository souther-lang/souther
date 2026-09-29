package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;

import java.math.BigInteger;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

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

    @Test
    void aLineWhoseCountTheHostCannotWriteOutHasAnIdentity() {
        CutPosition far = written(1, twoTo(Long.MIN_VALUE + 1));

        assertDoesNotThrow(far::canonical);
    }

    @Test
    void twoSpellingsOfOneLineThatFarOutAreOneIdentity() {
        CutPosition once = written(2, twoTo(Long.MIN_VALUE + 2));
        CutPosition twice = written(1, twoTo(Long.MIN_VALUE + 1));

        assertEquals(once.canonical(), twice.canonical());
    }
}
