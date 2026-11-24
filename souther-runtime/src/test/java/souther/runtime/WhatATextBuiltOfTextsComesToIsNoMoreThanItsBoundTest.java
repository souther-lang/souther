package souther.runtime;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.Normalization;
import souther.exact.BuiltTextBounds;

import java.math.BigInteger;
import java.util.List;
import java.util.Objects;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an operation of {@link Strings} answers of texts no longer than its bound is handed is no
 * longer than the bound its account says of them ({@link Strings#BUILT_TEXTS}); and copies and
 * padding, whose most a
 * {@code String} holds is handed in, do not stop where that most is the bound on the way.
 *
 * <p>Asked of the texts that do the most at a seam and in canonical form: a starter that took in
 * marks followed by a mark that composes with it in their place (U+01D6 + U+0323, one longer), a
 * bare mark that composes into what is before it, Hangul jamo that compose into a syllable, so that
 * padding with them comes short and builds its fill again, a text that grows when put in the form,
 * and one whose copies grow where they meet. Each in canonical form, as every {@code String} is.
 */
class WhatATextBuiltOfTextsComesToIsNoMoreThanItsBoundTest {

    private static final BuiltTextBounds ACCOUNT = Strings.BUILT_TEXTS;

    private static final List<String> TEXTS = List.of("", "a", "u", "ǖ", "̣", "́",
            "ᄀ", "ᅡ", "ᆨ", "가", "ཱི", "̈́", "가",
            "̣ǖ");

    private static String nfc(String text) {
        return Normalization.nfc(text);
    }

    private static BigInteger count(String text) {
        return BigInteger.valueOf(text.codePointCount(0, text.length()));
    }

    private static void heldTo(BuiltTextBounds.Bound bound, String answer, Supplier<String> what) {
        BigInteger most = answerOf(bound);
        assertTrue(count(answer).compareTo(most) <= 0
                        && most.compareTo(BigInteger.valueOf(onTheWayOf(bound))) <= 0,
                () -> what.get() + " is " + count(answer) + ", bound " + bound);
    }

    /** The bound on the answer, which every count here, handed as it is, gives. */
    private static BigInteger answerOf(BuiltTextBounds.Bound bound) {
        return Objects.requireNonNull(bound.answer(), "every count here is handed as it is");
    }

    /** The bound on the way, which every count here, handed as it is, gives. */
    private static long onTheWayOf(BuiltTextBounds.Bound bound) {
        return Objects.requireNonNull(bound.onTheWay(), "every count here is handed as it is")
                .longValueExact();
    }

    @Test
    void twoTextsJoinedAreNoLongerThanTheBound() {
        for (String one : TEXTS) {
            for (String other : TEXTS) {
                String a = nfc(one);
                String b = nfc(other);
                heldTo(ACCOUNT.appended(count(a), count(b)), Strings.append(a, b),
                        () -> a + " ++ " + b);
                heldTo(ACCOUNT.joinedWith(BigInteger.valueOf(3),
                                count(a).max(count(b)), count(b)),
                        Strings.join(List.of(a, b, a), b), () -> "join " + a + " " + b);
                heldTo(ACCOUNT.joinedWith(BigInteger.TWO, count(a).max(count(b)),
                                BigInteger.ZERO),
                        Strings.concat(List.of(a, b)), () -> "concat " + a + " " + b);
                String both = nfc(a + b);
                heldTo(ACCOUNT.reversed(count(both)), Strings.reverse(both),
                        () -> "reverse " + both);
                String around = nfc(a + "u" + a);
                heldTo(ACCOUNT.replaced(count(around), count(b)),
                        Strings.replace("u", b, around), () -> "replace u by " + b + " in " + a);
            }
        }
    }

    /**
     * Copies and padding measure what they build on the way against the most a {@code String}
     * holds, which is handed in here: held to the bound on the way as that most, none of them
     * stops, and what each answers is no longer than the bound on the answer. Padding with Hangul
     * jamo comes short where the copies compose into syllables, and builds its fill again for more.
     */
    @Test
    void copiesAndPaddingAreNoLongerThanTheBoundOnTheWayOrAtTheEnd() {
        for (String one : TEXTS) {
            String text = nfc(one);
            for (long count = 0; count <= 3; count++) {
                long n = count;
                BuiltTextBounds.Bound copies = ACCOUNT.repeated(count(text),
                        BigInteger.valueOf(n));
                heldTo(copies, Strings.repeat(text, n, onTheWayOf(copies)),
                        () -> n + " copies of " + text);
            }
            for (String each : TEXTS) {
                String fill = nfc(each);
                for (long width = 0; width <= 6; width++) {
                    long w = width;
                    BuiltTextBounds.Bound padded = ACCOUNT.padded(count(text),
                            BigInteger.valueOf(w), count(fill));
                    long most = onTheWayOf(padded);
                    for (boolean atStart : List.of(true, false)) {
                        heldTo(padded, Strings.pad(text, w, fill, atStart, most),
                                () -> text + " padded to " + w + " with " + fill);
                    }
                }
            }
        }
    }
}
