package souther.compiler.semantics;

import net.unit8.notation199x.Normalization;
import net.unit8.notation199x.WhiteSpace;
import org.junit.jupiter.api.Test;

import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the library states of a case conversion and white space ({@link OperationFacts}) is what
 * the run time answers, of every code point there is: a conversion answers no code point with
 * nothing, answers white space with white space alone — U+2000 is answered U+2002, which it is
 * canonically — and answers a code point that is not white space with some that are not; and no
 * white space is composed of a code point that is not, so the composition that follows a
 * conversion makes none of them white space.
 *
 * <p>Stated by hand of the Unicode version the run time converts by, and held to it here so that a
 * version that changes one is found where the statement is.
 */
class WhatTheLibraryStatesOfACaseConversionAndWhitespaceIsWhatItAnswersTest {

    private static List<String> broken(UnaryOperator<String> conversion) {
        List<String> out = new ArrayList<>();
        for (int cp = 0; cp <= Character.MAX_CODE_POINT; cp++) {
            if (cp >= 0xD800 && cp <= 0xDFFF) {
                continue;
            }
            String one = Character.toString(cp);
            String answer = conversion.apply(one);
            boolean white = WhiteSpace.contains(cp);
            if (answer.isEmpty()
                    || white != answer.codePoints().allMatch(WhiteSpace::contains)) {
                out.add(Integer.toHexString(cp));
            }
        }
        return out;
    }

    @Test
    void lowercasingAnswersWhiteSpaceWithItselfAndTheRestWithSomeThatIsNot() {
        assertEquals(List.of(), broken(Strings::lowercase));
    }

    @Test
    void uppercasingAnswersWhiteSpaceWithItselfAndTheRestWithSomeThatIsNot() {
        assertEquals(List.of(), broken(Strings::uppercase));
    }

    @Test
    void noWhiteSpaceIsComposedOfACodePointThatIsNot() {
        List<String> out = new ArrayList<>();
        for (int cp = 0; cp <= Character.MAX_CODE_POINT; cp++) {
            if ((cp >= 0xD800 && cp <= 0xDFFF) || !WhiteSpace.contains(cp)) {
                continue;
            }
            String parts = Normalization.normalize(Normalization.Form.NFD, Character.toString(cp));
            if (!parts.codePoints().allMatch(WhiteSpace::contains)) {
                out.add(Integer.toHexString(cp));
            }
        }
        assertEquals(List.of(), out);
    }
}
