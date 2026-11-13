package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import souther.compiler.types.ValueName;
import souther.runtime.Strings;

import java.util.List;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * {@link CaseMapping#applying} makes one mapping of a conversion applied to what the same
 * conversion made, and that is what the run time's conversions are: each is idempotent over every
 * code point, alone and with the letters a conversion looks at beside it (the closing sigma looks
 * at the letter before it, a composed result at the mark after it).
 */
class ACaseConversionRepeatedIsTheConversionOnceTest {

    private static final ValueName.Stdlib LOWERCASE = ValueName.Stdlib.operation("String",
            "lowercase");

    private static final ValueName.Stdlib UPPERCASE = ValueName.Stdlib.operation("String",
            "uppercase");

    private static final ValueName.Stdlib TRIM = ValueName.Stdlib.operation("String", "trim");

    @Test
    void aConversionOfItsOwnAnswerIsTheSameMapping() {
        assertSame(CaseMapping.LOWERCASE, CaseMapping.applying(LOWERCASE, CaseMapping.LOWERCASE));
        assertSame(CaseMapping.UPPERCASE, CaseMapping.applying(UPPERCASE, CaseMapping.UPPERCASE));
    }

    @Test
    void aConversionOfAnotherKeepsBothInTheirOrder() {
        assertEquals(new CaseMapping.Lowercase(CaseMapping.UPPERCASE),
                CaseMapping.applying(LOWERCASE, CaseMapping.UPPERCASE));
        assertEquals(new CaseMapping.Uppercase(new CaseMapping.Lowercase(CaseMapping.UPPERCASE)),
                CaseMapping.applying(UPPERCASE,
                        CaseMapping.applying(LOWERCASE, CaseMapping.UPPERCASE)));
        assertNull(CaseMapping.applying(TRIM, CaseMapping.LOWERCASE));
    }

    @Test
    void aLongChainOfOneConversionIsOneMappingAndOneRunOfTheOperationsItIsMadeOf() {
        CaseMapping chain = CaseMapping.NONE;
        for (int i = 0; i < 1_000; i++) {
            chain = CaseMapping.applying(LOWERCASE, chain);
        }
        assertEquals(CaseMapping.LOWERCASE, chain);
        assertEquals(List.of(LOWERCASE.qualified()), chain.operations());
    }

    @Test
    void theRunTimesLowercaseIsIdempotent() {
        idempotent(Strings::lowercase, "lowercase");
    }

    @Test
    void theRunTimesUppercaseIsIdempotent() {
        idempotent(Strings::uppercase, "uppercase");
    }

    private static void idempotent(UnaryOperator<String> conversion, String name) {
        for (int cp = 0; cp <= Character.MAX_CODE_POINT; cp++) {
            if (cp >= Character.MIN_SURROGATE && cp <= Character.MAX_SURROGATE) {
                continue;
            }
            String each = new String(Character.toChars(cp));
            for (String text : List.of(each, "a" + each, each + "a", "A" + each + "B",
                    "Σ" + each, each + "Σ", "Σ" + each + "Σ", each + "́", each + "̇")) {
                once(conversion, name, text);
            }
        }
    }

    private static void once(UnaryOperator<String> conversion, String name, String text) {
        String answer;
        try {
            answer = conversion.apply(text);
        } catch (RuntimeException stopped) {
            return;
        }
        assertEquals(answer, conversion.apply(answer),
                () -> name + " of its own answer differs for U+"
                        + Integer.toHexString(text.codePointAt(0)) + " in " + text);
    }
}
