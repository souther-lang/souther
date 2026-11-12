package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.abort.GetsPast;
import souther.runtime.Strings;

import net.unit8.notation199x.Normalization;

import java.lang.reflect.Method;
import java.math.BigInteger;
import java.util.List;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the run time answers of texts no longer than the bound is handed is no longer than the
 * bound {@link TextsBuilt} says of them.
 *
 * <p>Asked of the texts that do the most at a seam and in canonical form: a starter that took in
 * marks followed by a mark that composes with it in their place (U+01D6 + U+0323, one longer), a
 * bare mark that composes into what is before it, Hangul jamo that compose into a syllable, so that
 * padding with them comes short and builds its fill again, and a text that grows when put in the
 * form. Each in canonical form, as every {@code String} is.
 */
class WhatATextBuiltOfTextsComesToIsNoMoreThanItsBoundTest {

    private static final List<String> TEXTS = List.of("", "a", "u", "ǖ", "̣", "́",
            "ᄀ", "ᅡ", "ᆨ", "가", "ཱི", "̈́", "가",
            "̣ǖ");

    private static String nfc(String text) {
        return Normalization.nfc(text);
    }

    private static BigInteger count(String text) {
        return BigInteger.valueOf(text.codePointCount(0, text.length()));
    }

    /** Ceilings that are what each operand is: texts as long as they are, a list as many as it
     *  holds and each as long as the longest, a number as it is. */
    private static TextsBuilt.Ceilings exactly(Object... operands) {
        return new TextsBuilt.Ceilings() {
            @Override
            public BigInteger codePoints(int operand) {
                return count((String) operands[operand]);
            }

            @Override
            public BigInteger elements(int operand) {
                return BigInteger.valueOf(((List<?>) operands[operand]).size());
            }

            @Override
            public BigInteger codePointsOfEach(int operand) {
                return ((List<?>) operands[operand]).stream().map(each -> count((String) each))
                        .reduce(BigInteger.ZERO, BigInteger::max);
            }

            @Override
            public BigInteger number(int operand) {
                return BigInteger.valueOf((Long) operands[operand]);
            }
        };
    }

    private static void heldTo(GetsPast.TextBuilt built, String answer, Supplier<String> what,
                               Object... operands) {
        TextsBuilt.Bound bound = TextsBuilt.of(built, exactly(operands));
        assertTrue(count(answer).compareTo(bound.answer()) <= 0
                        && bound.answer().compareTo(bound.onTheWay()) <= 0,
                () -> what.get() + " is " + count(answer) + ", bound " + bound);
    }

    @Test
    void twoTextsJoinedAreNoLongerThanTheBound() {
        for (String one : TEXTS) {
            for (String other : TEXTS) {
                String a = nfc(one);
                String b = nfc(other);
                heldTo(new GetsPast.TextBuilt.Joined(0, 1), Strings.append(a, b),
                        () -> a + " ++ " + b, a, b);
                heldTo(new GetsPast.TextBuilt.JoinedWith(1, 0), Strings.join(List.of(a, b, a), b),
                        () -> "join " + a + " " + b, b, List.of(a, b, a));
                heldTo(new GetsPast.TextBuilt.JoinedWith(0, -1), Strings.concat(List.of(a, b)),
                        () -> "concat " + a + " " + b, List.of(a, b));
                heldTo(new GetsPast.TextBuilt.Reversed(0), Strings.reverse(a + b),
                        () -> "reverse " + a + b, nfc(a + b));
                heldTo(new GetsPast.TextBuilt.Replaced(2, 0, 1),
                        Strings.replace("u", b, nfc(a + "u" + a)),
                        () -> "replace u by " + b + " in " + a, "u", b, nfc(a + "u" + a));
            }
        }
    }

    /**
     * Copies and padding measure what they build on the way against the most a {@code String}
     * holds, which the run time takes as an argument here: held to the bound on the way as that
     * most, none of them stops, and what each answers is no longer than the bound on the answer.
     * Padding with Hangul jamo comes short where the copies compose into syllables, and builds its
     * fill again for more.
     */
    @Test
    void copiesAndPaddingAreNoLongerThanTheBoundOnTheWayOrAtTheEnd() throws ReflectiveOperationException {
        Method repeat = Strings.class.getDeclaredMethod("repeat", String.class, long.class,
                long.class);
        Method pad = Strings.class.getDeclaredMethod("pad", String.class, long.class, String.class,
                boolean.class, long.class);
        repeat.setAccessible(true);
        pad.setAccessible(true);
        for (String one : TEXTS) {
            String text = nfc(one);
            for (long count = 0; count <= 3; count++) {
                long n = count;
                GetsPast.TextBuilt copies = new GetsPast.TextBuilt.Copies(1, 0);
                String answer = (String) repeat.invoke(null, text, n,
                        TextsBuilt.of(copies, exactly(n, text)).onTheWay().longValueExact());
                heldTo(copies, answer, () -> n + " copies of " + text, n, text);
            }
            for (String each : TEXTS) {
                String fill = nfc(each);
                for (long width = 0; width <= 6; width++) {
                    long w = width;
                    GetsPast.TextBuilt padded = new GetsPast.TextBuilt.Padded(2, 0, 1);
                    long most = TextsBuilt.of(padded, exactly(w, fill, text)).onTheWay()
                            .longValueExact();
                    for (boolean atStart : List.of(true, false)) {
                        String answer = (String) pad.invoke(null, text, w, fill, atStart, most);
                        heldTo(padded, answer,
                                () -> text + " padded to " + w + " with " + fill, w, fill, text);
                    }
                }
            }
        }
    }
}
