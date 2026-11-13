package souther.compiler.values;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import souther.compiler.regex.PatternPlan;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Values held to at least some code points are shown to hold one where the language has a string
 * of that length as written, or of every length from it on, and not because it has a shorter one.
 * A length held as a number is asked of the set this way, whatever length it names.
 */
class AStringOfAtLeastSomeCodePointsIsShownWhereTheLanguageReachesThatLengthTest {

    /** Runs of letters, longer than any machine this compiler builds is long: there is one, and
     *  one of exactly that many where that is few enough to walk to. */
    @Test
    void runsOfLettersHoldOneOfAnyLengthAStringCanHave() {
        assertTrue(ValuesWithin.longerThan(matching("[a-z]*"), 100_000).shownToHoldAValue());
        assertTrue(new ValuesWithin(matching("[a-z]*"), 255, 255L).shownToHoldAValue());
    }

    /** Strings of pairs of letters hold one of four code points and none of three, which a
     *  shorter string of them says nothing of. */
    @Test
    void aLanguageOfPairsHoldsOneOfAnEvenLengthOnly() {
        ValueSet pairs = matching("(ab)*");

        assertTrue(new ValuesWithin(pairs, 4, 4L).shownToHoldAValue());
        assertFalse(new ValuesWithin(pairs, 3, 3L).shownToHoldAValue());
    }

    /** A language whose strings are all short holds none longer, however long. */
    @Test
    void aLanguageOfShortStringsHoldsNoneLonger() {
        assertTrue(ValuesWithin.longerThan(matching("[a-z]{0,3}"), 3).shownToHoldNone());
        assertFalse(ValuesWithin.longerThan(matching("[a-z]{0,3}"), 3).shownToHoldAValue());
    }

    private static ValueSet matching(String regex) {
        PatternRead said = PatternParser.read(regex);
        return ValueSet.matching(PatternPlan.of(
                        assertInstanceOf(PatternRead.Read.class, said, regex).meaning())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()));
    }
}
