package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether one name is under another is asked of the fields, never of the text.
 *
 * <p>What reads this is a stop: a reading that stopped at a name is short of the rules there and of
 * every rule under it, and of nothing else. Asked of the spelling, {@code ab} is under {@code a}
 * because the letters say so — and a stop at one field would take the field beside it with it.
 *
 * <p>The law and not a corpus. These are the cases the answer is defined by, and the one the
 * spelling gets wrong is among them.
 */
class ANameIsUnderAnotherByItsStepsAndNotItsSpellingTest {

    private static final RuleKey A = RuleKey.of("a");
    private static final RuleKey AB = RuleKey.of("ab");
    private static final RuleKey A_B = new RuleKey(List.of("a", "b"));

    /** The value the rules are of is every name's first step of none, so it is over all of them. */
    @Test
    void theValueItselfIsOverEveryName() {
        assertTrue(A.isAtOrUnder(RuleKey.THE_VALUE));
        assertTrue(A_B.isAtOrUnder(RuleKey.THE_VALUE));
        assertTrue(RuleKey.THE_VALUE.isAtOrUnder(RuleKey.THE_VALUE));
    }

    /** A name is under itself: a stop at a name is short of the rules written at it. */
    @Test
    void aNameIsUnderItself() {
        assertTrue(A.isAtOrUnder(A));
    }

    /** And under the names it is read through. */
    @Test
    void aNameIsUnderWhatItIsReadThrough() {
        assertTrue(A_B.isAtOrUnder(A));
        assertFalse(A.isAtOrUnder(A_B), "what is read through a name is not over it");
    }

    /**
     * And a name that merely starts with the same letters is under nothing of the sort.
     *
     * <p>The case a spelling gets wrong, and the reason the steps are what is compared: read as
     * text, {@code ab} follows {@code a} and a stop at {@code a} would silence the field beside it.
     */
    @Test
    void aNameThatOnlyReadsAlikeIsUnderNothing() {
        assertFalse(AB.isAtOrUnder(A));
        assertFalse(A.isAtOrUnder(AB));
    }

    /**
     * A step is one field, so nothing can put two into one.
     *
     * <p>Written with a dot, a name would be one step to whoever compared the steps and two to
     * whoever printed it — which is the two answers this type is for.
     */
    @Test
    void aStepIsOneField() {
        assertThrows(IllegalArgumentException.class, () -> new RuleKey(List.of("a.b")));
        assertThrows(IllegalArgumentException.class, () -> new RuleKey(List.of("")));
    }

    /** What a report writes for one, which is a rendering and not how one is compared. */
    @Test
    void theSpellingIsForAReader() {
        assertEquals("a.b", A_B.toString());
        assertEquals("", RuleKey.THE_VALUE.toString());
    }
}
