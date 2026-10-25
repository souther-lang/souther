package souther.compiler.values;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import souther.compiler.numeric.Text;
import souther.compiler.regex.Language;
import souther.compiler.regex.PatternPlan;

import java.util.HashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A language holds the strings a rule leaves, and a {@code String} holds only the ones in
 * Normalization Form C. That a language is not empty bounds the values and shows none of them.
 */
class ALanguageBoundsTheValuesAndProvesNoneExistsTest {

    /** {@code a} then a combining acute is held as one code point, so no value starts that way. */
    @Test
    void aLanguageOfStringsNormalizationChangesIsNotShownToHoldAValue() {
        assertEquals(Emptiness.UNDECIDED, TextExtents.holdsAValue(languageOf("a\\x{301}.*")));
    }

    /** A string a form leaves alone is a value however the language reaches it. */
    @Test
    void aStringHeldAsWrittenShowsAValueBesideOnesThatAreNot() {
        assertEquals(Emptiness.NONEMPTY, TextExtents.holdsAValue(languageOf("a\\x{301}|bb")));
        assertEquals(Emptiness.NONEMPTY, TextExtents.holdsAValue(languageOf("[a-z]+")));
    }

    /**
     * A combining mark alone is in the form, so it is a value this reading cannot show; it must
     * not be read as none.
     */
    @Test
    void aCombiningMarkAloneIsNotTakenForNoValue() {
        assertEquals(Emptiness.UNDECIDED, TextExtents.holdsAValue(languageOf("\\x{301}")));
    }

    @Test
    void aLanguageHoldingNothingHoldsNoValue() {
        Language none = Language.ofWords(Set.of(),
                PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        assertEquals(Emptiness.EMPTY, TextExtents.holdsAValue(none));
    }

    /** The ends of a run are lines drawn at strings, so they have to be strings a value is. */
    @Test
    void aRunWhoseEndIsNotAValueDrawsNoLine() {
        assertEquals(new TextExtent.NotEstablished(),
                TextExtents.of(languageOf("a\\x{301}[\\s\\S]*")));
        assertEquals(new TextExtent.One(Text.of("JP"), Text.of("JQ")),
                TextExtents.of(languageOf("JP[\\s\\S]*")));
    }

    /** Finitely many strings left out can be every string of one length, and not only the empty
     *  one: no string of ASCII alone is changed by the form, so a length is left without a value
     *  only when as many of them are out as there are. */
    @Test
    void everyStringOfALengthLeftOutLeavesNoValueOfThatLength() {
        Set<Value> allButOne = new HashSet<>();
        for (char each = 0; each < 127; each++) {
            allButOne.add(Value.text(String.valueOf(each)));
        }
        Set<Value> all = new HashSet<>(allButOne);
        all.add(Value.text(String.valueOf((char) 127)));

        assertTrue(TextExtents.reachesEveryLength(new ValueSet.Cofinite(allButOne), n -> n == 1, false));
        assertFalse(TextExtents.reachesEveryLength(new ValueSet.Cofinite(all), n -> n == 1, false));
        assertTrue(TextExtents.reachesEveryLength(new ValueSet.Cofinite(all), n -> n == 2, false),
                "a length none of them has is left whole");
    }

    private static Language languageOf(String pattern) {
        PatternRead read = PatternParser.read(pattern);
        assertInstanceOf(PatternRead.Read.class, read, pattern + " is read");
        Language made = PatternPlan.of(((PatternRead.Read) read).meaning())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        assertNotNull(made, pattern + " compiles");
        return made;
    }
}
