package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.ExactRatio;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Two spaces of levels made the same way are the same space.
 *
 * <p>A value that holds a space, as a {@link Standing} does, is built again for each asker from the
 * same quantity. Told apart by identity, the space would make two of them differ by nothing either
 * says. So a space is its kind and what that kind was given, and the kind counts: the whole numbers
 * cut at a step and the decimals cut at the same step are two spaces with one number between them.
 */
class ASpaceOfLevelsIsKnownByWhatItIsMadeFromTest {

    private static final ExactRatio TWO = ExactRatio.of(2);

    @Test
    void theSameKindGivenTheSameIsTheSameSpace() {
        assertTheSameSpace(LevelSpace.steppingBy(ExactRatio.ONE),
                LevelSpace.steppingBy(ExactRatio.ONE));
        assertTheSameSpace(LevelSpace.overFiniteDecimals(TWO),
                LevelSpace.overFiniteDecimals(TWO));
        assertTheSameSpace(LevelSpace.onACarrier(Carrier.WHOLE),
                LevelSpace.onACarrier(Carrier.WHOLE));
        assertTheSameSpace(LevelSpace.onlyWhereTheyMeet(), LevelSpace.onlyWhereTheyMeet());
    }

    @Test
    void aSpaceOnNoCarrierIsAKindToo() {
        assertTheSameSpace(LevelSpace.onACarrier(null), LevelSpace.onACarrier(null));
        assertNotEquals(LevelSpace.onACarrier(null), LevelSpace.onACarrier(Carrier.WHOLE));
    }

    @Test
    void theSameKindGivenAnotherIsAnotherSpace() {
        assertNotEquals(LevelSpace.steppingBy(ExactRatio.ONE), LevelSpace.steppingBy(TWO));
        assertNotEquals(LevelSpace.overFiniteDecimals(ExactRatio.ONE),
                LevelSpace.overFiniteDecimals(TWO));
        assertNotEquals(LevelSpace.onACarrier(Carrier.WHOLE), LevelSpace.onACarrier(Carrier.DENSE));
    }

    /** The control for the kind counting: one number given to two kinds. */
    @Test
    void anotherKindGivenTheSameIsAnotherSpace() {
        assertNotEquals(LevelSpace.steppingBy(ExactRatio.ONE),
                LevelSpace.overFiniteDecimals(ExactRatio.ONE));
        assertNotEquals(LevelSpace.steppingBy(ExactRatio.ONE),
                LevelSpace.onACarrier(Carrier.WHOLE));
        assertNotEquals(LevelSpace.onlyWhereTheyMeet(), LevelSpace.onACarrier(null));
    }

    /** A space named for what it leaves out is one of the kinds and not a kind of its own. */
    @Test
    void theDenseSpaceIsTheFiniteDecimalsAtOne() {
        assertTheSameSpace(LevelSpace.dense(), LevelSpace.overFiniteDecimals(ExactRatio.ONE));
    }

    private static void assertTheSameSpace(LevelSpace one, LevelSpace other) {
        assertEquals(one, other);
        assertEquals(one.hashCode(), other.hashCode(), "equal spaces hash alike");
    }
}
