package souther.compiler.jvm;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * What a {@link ClassFileImage} is: the octets it was made of, compared by what they say.
 *
 * <p>The whole of what the answers holding one rest on. A store stops work by comparing an answer
 * with the one it replaces, so two of these made from the same bytes have to be equal and two made
 * from different bytes have to not be — and neither can turn on which array they were handed.
 */
class AClassFileIsWhatItsBytesSayTest {

    /** Every octet there is, so nothing about the carrier turns on which values went through it. */
    private static byte[] everyOctet() {
        byte[] all = new byte[256];
        for (int i = 0; i < all.length; i++) {
            all[i] = (byte) i;
        }
        return all;
    }

    @Test
    void everyByteComesBackAsItWentIn() {
        assertArrayEquals(everyOctet(), ClassFileImage.of(everyOctet()).bytes());
    }

    @Test
    void twoOfOneContentAreOneValue() {
        assertEquals(ClassFileImage.of(everyOctet()), ClassFileImage.of(everyOctet()));
        assertEquals(ClassFileImage.of(everyOctet()).hashCode(),
                ClassFileImage.of(everyOctet()).hashCode());
    }

    @Test
    void oneByteApartIsNotOneValue() {
        byte[] moved = everyOctet();
        moved[128] = (byte) (moved[128] + 1);
        assertNotEquals(ClassFileImage.of(everyOctet()), ClassFileImage.of(moved));
    }

    @Test
    void anEmptyOneIsAValueToo() {
        assertEquals(ClassFileImage.of(new byte[0]), ClassFileImage.of(new byte[0]));
        assertEquals(0, ClassFileImage.of(new byte[0]).size());
    }

    @Test
    void sizeIsHowManyBytesThereAre() {
        assertEquals(256, ClassFileImage.of(everyOctet()).size());
    }

    /** What was handed over is not what is held: writing into it afterwards changes nothing. */
    @Test
    void writingIntoTheArrayItWasMadeFromChangesNothing() {
        byte[] handed = everyOctet();
        ClassFileImage image = ClassFileImage.of(handed);
        handed[0] = (byte) 0xFF;
        assertEquals(ClassFileImage.of(everyOctet()), image);
        assertArrayEquals(everyOctet(), image.bytes());
    }

    /** And what it hands out is not what it holds. */
    @Test
    void writingIntoTheArrayItHandsOutChangesNothing() {
        ClassFileImage image = ClassFileImage.of(everyOctet());
        byte[] taken = image.bytes();
        taken[0] = (byte) 0xFF;
        assertArrayEquals(everyOctet(), image.bytes());
        assertEquals(ClassFileImage.of(everyOctet()), image);
    }
}
