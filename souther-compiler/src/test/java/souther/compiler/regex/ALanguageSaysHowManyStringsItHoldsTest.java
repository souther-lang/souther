package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * How many strings a language holds is the paths of its one machine counted, each step as many
 * ways as the code points it reads, and no number where a string goes round a loop. The strings
 * are counted and not listed: a count past any figure a listing stops at is what it is.
 */
class ALanguageSaysHowManyStringsItHoldsTest {

    private static Language language(String regex) {
        Language said = PatternPlan.of(assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        assertNotNull(said, regex);
        return said;
    }

    @Test
    void aFormatOfFixedPartsHoldsTheProductOfTheirSizes() {
        assertEquals(BigInteger.valueOf(26 * 26 * 26), language("[A-Z]{3}").howManyStrings());
        assertEquals(BigInteger.valueOf(10_000_000_000L), language("[0-9]{10}").howManyStrings());
    }

    @Test
    void whereTheLengthMayVaryEachLengthIsCounted() {
        // The empty string, two of one letter and four of two.
        assertEquals(BigInteger.valueOf(1 + 2 + 4), language("[ab]{0,2}").howManyStrings());
    }

    @Test
    void wordsAreCountedOnceEach() {
        assertEquals(BigInteger.valueOf(3), Language.ofWords(List.of("a", "bc", "bd"),
                PatternPlan.Budget.OF_ADMITTED_VALUES.meter()).howManyStrings());
    }

    @Test
    void aLoopLeavesNoNumber() {
        assertNull(language("[a-z]+").howManyStrings());
        assertNull(Language.EVERY_STRING.howManyStrings());
    }

    @Test
    void nothingIsNoStrings() {
        assertEquals(BigInteger.ZERO, language("[a-z]").and(language("[0-9]"),
                PatternPlan.Budget.OF_ADMITTED_VALUES.meter()).howManyStrings());
    }
}
