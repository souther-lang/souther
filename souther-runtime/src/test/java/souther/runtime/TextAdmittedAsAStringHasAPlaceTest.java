package souther.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Text from outside is a {@code String} only where its canonical value has a place (spec
 * §what-a-string-holds). The bound is the carrier's, so these ask {@link Strings#admission} of a
 * carrier that holds a few units: text that long cannot be built to ask the JVM's own.
 */
class TextAdmittedAsAStringHasAPlaceTest {

    private static final String HIGH = String.valueOf((char) 0xD800);

    /** U+0344 canonicalizes to two marks, so what arrives one unit long is two units as a String. */
    private static final String EXPANDS = "̈́";

    /** {@code e} and a combining acute, which canonicalize to the one character {@code é}. */
    private static final String SHRINKS = "é";

    @Test
    void textWithinTheBoundIsAdmittedCanonical() {
        assertEquals(new TextAdmission.Admitted("abc"), Strings.admission("abc", 3));
        assertEquals(new TextAdmission.Admitted("é"), Strings.admission(SHRINKS, 1));
    }

    @Test
    void whatIsMeasuredIsTheCanonicalValueAndNotTheTextThatArrived() {
        // The text is longer than the bound and the String it is, is not.
        assertEquals(2, SHRINKS.length());
        assertInstanceOf(TextAdmission.Admitted.class, Strings.admission(SHRINKS, 1));
        // The other way round: one unit arrived, and two are what it would be.
        assertEquals(1, EXPANDS.length());
        assertInstanceOf(TextAdmission.NoPlace.class, Strings.admission(EXPANDS, 1));
        assertInstanceOf(TextAdmission.Admitted.class, Strings.admission(EXPANDS, 2));
    }

    @Test
    void textLongerThanTheBoundHasNoPlace() {
        assertEquals(new TextAdmission.NoPlace(), Strings.admission("abcd", 3));
        assertEquals(new TextAdmission.Admitted(""), Strings.admission("", 0));
        assertEquals(new TextAdmission.NoPlace(), Strings.admission("a", 0));
    }

    @Test
    void halfAPairIsNotTextWhateverTheBound() {
        assertEquals(new TextAdmission.NotText(0), Strings.admission(HIGH, 0));
        assertEquals(new TextAdmission.NotText(1), Strings.admission("a" + HIGH, 100));
    }

    /** What a String is admitted as is what every operation over it can answer: an identity for
     *  {@code append} is not refused for want of a place. */
    @Test
    void whatIsAdmittedIsAnIdentityForAppend() {
        for (String text : new String[] {"", "abc", SHRINKS, EXPANDS, "𠮷"}) {
            String admitted = Strings.admit(text);
            assertEquals(admitted, Strings.append("", admitted));
            assertEquals(admitted, Strings.append(admitted, ""));
        }
    }

    @Test
    void theDecodersQuestionsAreAnsweredFromWhatAdmissionSaid() {
        TextAdmission noPlace = new TextAdmission.NoPlace();
        TextAdmission notText = new TextAdmission.NotText(0);
        TextAdmission admitted = new TextAdmission.Admitted("a");
        assertEquals(false, Strings.isText(notText));
        assertEquals(true, Strings.isText(noPlace));
        assertEquals(true, Strings.isText(admitted));
        assertEquals(false, Strings.hasPlace(noPlace));
        assertEquals(true, Strings.hasPlace(notText));
        assertEquals(true, Strings.hasPlace(admitted));
        assertEquals("a", Strings.textOf(admitted));
    }

    @Test
    void theOtherWaysOfAskingAgreeWithAdmission() {
        assertEquals("abc", Strings.admitted("abc"));
        assertNull(Strings.admitted(HIGH));
        assertThrows(ConstraintViolation.class, () -> Strings.admit(HIGH));
    }
}
