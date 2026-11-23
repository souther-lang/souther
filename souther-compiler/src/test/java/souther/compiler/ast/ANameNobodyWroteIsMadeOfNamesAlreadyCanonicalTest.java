package souther.compiler.ast;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A name a pass makes is taken as the name it is, and one that was not canonicalized where it
 * entered is a mistake of the pass and not a name ({@link WrittenName#synthetic}).
 *
 * <p>Asked by an assertion, so that every model the tests compile holds every pass to it and a
 * compile of an author's pays for none of it.
 */
class ANameNobodyWroteIsMadeOfNamesAlreadyCanonicalTest {

    /** か + a combining voiced sound mark. */
    private static final String DECOMPOSED = "が";
    /** The same kana as one code point. */
    private static final String CANONICAL = "が";

    @Test
    void aSpellingFromOutsideIsRefused() {
        assertThrows(AssertionError.class, () -> WrittenName.synthetic(DECOMPOSED, null));
    }

    @Test
    void aNameIsTakenAsItIsAndJoinedWithAMemberIsCanonicalStill() {
        WrittenName name = WrittenName.synthetic(CANONICAL, null);

        assertEquals(CANONICAL, name.canonical());
        assertEquals(CANONICAL + "." + CANONICAL, name.then(name).canonical());
    }
}
