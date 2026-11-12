package souther.compiler.partition;

import java.util.List;

import net.unit8.notation199x.pattern.Meter;

import org.junit.jupiter.api.Test;

import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.StringsInsideStrings;
import souther.compiler.semantics.CaseMapping;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a conversion answers is held in two languages: values, from which strings are made, and
 * the strings it leaves as they stand, which include sequences that are no value and so say only
 * of a value that it is an answer. {@code a} followed by a combining acute is such a sequence: no
 * {@code String} holds it, and {@code a} is inside it.
 */
class WhatAConversionAnswersKeepsValuesApartFromWhatItLeavesAsItStandsTest {

    private static final Meter METER = PatternPlan.Budget.OF_THE_PIECES_OF_A_LANGUAGE.meter();

    private static final String NOT_NFC = "á";

    private static WhatAConversionAnswers of(CaseMapping through, String... words) {
        Language partner = Language.ofWords(List.of(words), METER);
        return WhatAConversionAnswers.of(partner, through, METER);
    }

    private static Language inside(Language outer) {
        return StringsInsideStrings.standingIn(outer, StringsInsideStrings.Where.ANYWHERE, METER);
    }

    @Test
    void aSequenceThatIsNoValueIsAskedOfOnlyByTheEquality() {
        WhatAConversionAnswers answers = of(CaseMapping.LOWERCASE, NOT_NFC, "zz");
        assertFalse(answers.forDerivation().has(NOT_NFC));
        assertTrue(answers.forDerivation().has("zz"));
        assertTrue(answers.forEquality(METER).canBe().has(NOT_NFC));
    }

    /** Where strings are made from the answers, none is made from the sequence that is no value:
     *  {@code a} is inside it, and is the answer's of no value. */
    @Test
    void nothingIsMadeFromASequenceThatIsNoValue() {
        WhatAConversionAnswers answers = of(CaseMapping.LOWERCASE, NOT_NFC, "zz");
        Language made = inside(answers.forDerivation());
        assertFalse(made.has("a"));
        assertTrue(made.has("z"));
        // What would be made from the strings an equality is shown at: the hazard kept apart.
        assertTrue(inside(answers.forEquality(METER).canBe()).has("a"));
    }

    @Test
    void aValueTheConversionLeavesAsItStandsIsShownByTheEquality() {
        // U+0301 alone is a value, and outside the strings the conversion is exactly a map on.
        WhatAConversionAnswers answers = of(CaseMapping.LOWERCASE, "́", "ABC");
        WhatAConversionAnswers.Shown asked = answers.forEquality(METER);
        assertTrue(asked.canBe().has("́"));
        assertTrue(asked.canBe().has("abc"));
        assertFalse(asked.canBe().has("ABC"));
        assertFalse(answers.forDerivation().has("́"));
        assertTrue(asked.mayBe().has("́"));
    }

    @Test
    void whatIsShownIsAmongWhatMayBe() {
        WhatAConversionAnswers.Shown asked =
                of(CaseMapping.LOWERCASE, NOT_NFC, "zz", "ΟΣ", "İ").forEquality(METER);
        assertTrue(asked.canBe().and(asked.mayBe().not(METER), METER).isEmpty());
    }

    /** Of two conversions in turn a string it leaves as it stands is not its own answer. */
    @Test
    void twoConversionsLeaveNothingAsItStands() {
        CaseMapping both = new CaseMapping.Lowercase(CaseMapping.UPPERCASE);
        WhatAConversionAnswers.Shown asked = of(both, "ß", "z").forEquality(METER);
        assertFalse(asked.canBe().has("ß"));
        assertTrue(asked.canBe().has("z"));
    }

    @Test
    void noConversionShowsValuesAlone() {
        WhatAConversionAnswers.Shown asked = of(CaseMapping.NONE, "zz", "́")
                .forEquality(METER);
        assertTrue(asked.canBe().has("zz"));
        assertFalse(asked.canBe().has("́"));
    }
}
