package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import souther.compiler.types.ValueName;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * {@link CaseMapping#applying} makes one mapping of a conversion applied to what the same
 * conversion made, and that is what the run time's conversions are: each is idempotent over the
 * strings of up to three of the code points a conversion turns on, which are where context (the
 * closing sigma), widening (ß) and composition (marks, jamo) could make a second application
 * differ.
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

    /** The code points a conversion turns on: the closing sigma, the dotted capital I, the sharp s
     *  in both cases, combining marks that compose, a titlecase letter, the Kelvin sign, and the
     *  jamo that compose into a syllable. */
    private static final List<String> ALPHABET = List.of("a", "A", "Σ", "σ", "ς", "İ", "i", "ß",
            "ẞ", "́", "̇", "̣", "ǅ", "K", "ᄀ", "ᅡ");

    private static void idempotent(UnaryOperator<String> conversion, String name) {
        List<String> every = new ArrayList<>(ALPHABET);
        for (String first : ALPHABET) {
            for (String second : ALPHABET) {
                every.add(first + second);
                for (String third : ALPHABET) {
                    every.add(first + second + third);
                }
            }
        }
        for (String text : every) {
            String answer = conversion.apply(text);
            assertEquals(answer, conversion.apply(answer),
                    () -> name + " of its own answer differs in " + text);
        }
    }
}
