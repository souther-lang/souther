package souther.runtime;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * {@link Strings#admission} lets in text only where it is made of scalar values, and lets it in as
 * NFC.
 *
 * <p>What order two such strings come in is 199x-notation's {@code ScalarValues.compare}, which
 * {@link Strings#compare} hands them to and which is tested there.
 */
class OnlyTextMadeOfScalarValuesIsLetInTest {

    @Test
    void textMadeOfScalarValuesIsLetInCanonical() {
        String pair = new String(Character.toChars(0x10000));
        assertEquals(pair, Strings.admit(pair));
        assertEquals("", Strings.admit(""));
        // か and a combining voiced sound mark, which is が.
        assertEquals(String.valueOf((char) 0x304C),
                Strings.admit(new String(new char[] {0x304B, 0x3099})));
    }

    @Test
    void textHoldingHalfAPairIsNotLetIn() {
        String high = String.valueOf((char) 0xD800);
        String low = String.valueOf((char) 0xDC00);
        for (String half : List.of(high, low, low + high, "a" + high, high + "a", high + high)) {
            assertInstanceOf(TextAdmission.NotText.class, Strings.admission(half));
            assertThrows(ConstraintViolation.class, () -> Strings.admit(half));
        }
    }
}
