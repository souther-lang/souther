package souther.compiler.semantics;

import org.junit.jupiter.api.Test;

import souther.compiler.types.ValueName;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.List;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link CaseMapping#applying} makes one mapping of a conversion applied to what the same
 * conversion made, and that is what the run time's conversions are: each is idempotent over the
 * strings of up to three of the code points a conversion turns on, which are where context (the
 * closing sigma), widening (ß) and composition (marks, jamo) could make a second application
 * differ. A chain of conversions that alternate is held to the same strings: what it makes is what
 * the chain two conversions shorter makes, past the length the mapping keeps.
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
    void aLongChainThatAlternatesIsAsLongAsAMappingOfItsOwnAtMost() {
        CaseMapping chain = CaseMapping.NONE;
        for (int i = 0; i < 1_000; i++) {
            chain = CaseMapping.applying(i % 2 == 0 ? LOWERCASE : UPPERCASE, chain);
        }
        int most = chain instanceof CaseMapping.Lowercase
                ? CaseMapping.MOST_ALTERNATING_ENDING_IN_LOWERCASE
                : CaseMapping.MOST_ALTERNATING_ENDING_IN_UPPERCASE;
        int kept = chain.doneSoFar().size();
        assertTrue(kept <= most, () -> "a chain of " + kept + " conversions is kept");
    }

    @Test
    void aChainOfAlternatingConversionsMakesWhatItsMappingMakes() {
        for (boolean endsInLowercase : new boolean[] {true, false}) {
            for (int length = 1; length <= 6; length++) {
                String applied = "";
                CaseMapping mapping = CaseMapping.NONE;
                for (int fromTheLast = length - 1; fromTheLast >= 0; fromTheLast--) {
                    boolean lowercase = (fromTheLast % 2 == 0) == endsInLowercase;
                    applied += lowercase ? "L" : "U";
                    mapping = CaseMapping.applying(lowercase ? LOWERCASE : UPPERCASE, mapping);
                }
                String written = applied;
                String done = String.join("", mapping.operations().stream()
                        .map(operation -> operation.equals(LOWERCASE.qualified()) ? "L" : "U")
                        .toList());
                for (String text : texts()) {
                    assertEquals(chain(text, written), chain(text, done),
                            () -> written + " is not " + done + " in " + text);
                }
            }
        }
    }

    @Test
    void aChainShorterThanTheBoundIsNotTheOneTwoShorter() {
        // lowercase(uppercase(lowercase(x))) and lowercase(uppercase(x)) differ on the capital sharp
        // s; uppercase(lowercase(uppercase(x))) and uppercase(lowercase(x)) on a ypogegrammeni
        // before a mark.
        assertNotEquals(chain("ẞ", "UL"), chain("ẞ", "LUL"));
        assertNotEquals(chain("̀ͅ", "LU"), chain("̀ͅ", "ULU"));
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
     *  in both cases, combining marks that compose, a titlecase letter, the Kelvin sign, the
     *  jamo that compose into a syllable, and the ypogegrammeni with a mark that follows it. */
    private static final List<String> ALPHABET = List.of("a", "A", "Σ", "σ", "ς", "İ", "i", "ß",
            "ẞ", "́", "̇", "̣", "ǅ", "K", "ᄀ", "ᅡ", "ͅ", "̀");

    /** {@code text} with each conversion of {@code applied} made of it in turn: {@code L} is
     *  lowercase, {@code U} uppercase. */
    private static String chain(String text, String applied) {
        String made = text;
        for (char each : applied.toCharArray()) {
            made = each == 'L' ? Strings.lowercase(made) : Strings.uppercase(made);
        }
        return made;
    }

    /** Each code point of {@link #ALPHABET}, and each string of two and of three of them. */
    private static List<String> texts() {
        List<String> every = new ArrayList<>(ALPHABET);
        for (String first : ALPHABET) {
            for (String second : ALPHABET) {
                every.add(first + second);
                for (String third : ALPHABET) {
                    every.add(first + second + third);
                }
            }
        }
        return every;
    }

    private static void idempotent(UnaryOperator<String> conversion, String name) {
        for (String text : texts()) {
            String answer = conversion.apply(text);
            assertEquals(answer, conversion.apply(answer),
                    () -> name + " of its own answer differs in " + text);
        }
    }
}
