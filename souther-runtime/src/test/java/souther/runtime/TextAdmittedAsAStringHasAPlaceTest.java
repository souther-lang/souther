package souther.runtime;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;
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

    /** A decoder says each refusal at the path, with Raoh's one code and a message of its own. */
    @Test
    void aDecodersLeafSaysWhichRefusalItWas() {
        Path at = Path.ROOT.append("s");
        assertEquals(new Ok<>("a"), TextLeaf.answer(new TextAdmission.Admitted("a"), at));
        Issue halfAPair = issueOf(TextLeaf.answer(new TextAdmission.NotText(0), at));
        Issue noPlace = issueOf(TextLeaf.answer(new TextAdmission.NoPlace(), at));
        assertEquals(TextLeaf.REFUSED, halfAPair.code());
        assertEquals(TextLeaf.REFUSED, noPlace.code());
        assertEquals(TextLeaf.HALF_A_PAIR, halfAPair.message());
        assertEquals(TextLeaf.NO_PLACE, noPlace.message());
        assertEquals("/s", noPlace.path().toJsonPointer());
    }

    private static Issue issueOf(Result<String> result) {
        return assertInstanceOf(Err.class, result).issues().asList().get(0);
    }

    @Test
    void theOtherWaysOfAskingAgreeWithAdmission() {
        assertEquals("abc", Strings.admitted("abc"));
        assertNull(Strings.admitted(HIGH));
        assertThrows(ConstraintViolation.class, () -> Strings.admit(HIGH));
    }
}
