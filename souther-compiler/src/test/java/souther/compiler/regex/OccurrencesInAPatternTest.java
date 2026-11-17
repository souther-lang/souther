package souther.compiler.regex;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternMeaning;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.OptionalLong;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The most times a code point stands in a string a pattern accepts, read off the pattern, is the
 * most the strings the machine of the pattern accepts hold it — and is no ceiling where some
 * accepted string holds it as often as it likes.
 */
class OccurrencesInAPatternTest {

    private static final int AT = '@';
    private static final int NO_CEILING = PatternMeaning.Repeated.NO_CEILING;

    private static final PatternMeaning LETTER = new PatternMeaning.Symbols(
            CodePoints.between('a', 'z'));
    private static final PatternMeaning AT_SIGN = new PatternMeaning.Symbols(
            CodePoints.between(AT, AT));
    private static final PatternMeaning LETTER_OR_AT = new PatternMeaning.Symbols(
            CodePoints.between('a', 'z').or(CodePoints.between(AT, AT)));
    private static final PatternMeaning NEVER = new PatternMeaning.Never();
    private static final PatternMeaning NOTHING = new PatternMeaning.Nothing();

    private static PatternMeaning repeated(PatternMeaning what, int least, int most) {
        return new PatternMeaning.Repeated(what, least, most);
    }

    private static PatternMeaning inTurn(PatternMeaning... parts) {
        return new PatternMeaning.InTurn(List.of(parts));
    }

    private static PatternMeaning eitherOf(PatternMeaning... arms) {
        return new PatternMeaning.EitherOf(List.of(arms));
    }

    private static OptionalLong most(PatternMeaning meaning) {
        return OccurrencesInAPattern.most(meaning, AT);
    }

    @Test
    void aSignBetweenTwoUnboundedRunsStandsOnce() {
        assertEquals(OptionalLong.of(1), most(inTurn(repeated(LETTER, 0, NO_CEILING), AT_SIGN,
                repeated(LETTER, 0, NO_CEILING))));
    }

    @Test
    void aRunThatMayHoldTheSignHasNoCeiling() {
        assertEquals(OptionalLong.empty(), most(repeated(LETTER_OR_AT, 0, NO_CEILING)));
        assertEquals(OptionalLong.empty(), most(inTurn(LETTER, repeated(AT_SIGN, 1,
                NO_CEILING))));
    }

    @Test
    void aRunThatCannotHoldTheSignHoldsNone() {
        assertEquals(OptionalLong.of(0), most(repeated(LETTER, 0, NO_CEILING)));
        assertEquals(OptionalLong.of(0), most(NOTHING));
    }

    @Test
    void aBoundedRepetitionHoldsTheSignAsOftenAsItIsRepeated() {
        assertEquals(OptionalLong.of(3), most(repeated(AT_SIGN, 0, 3)));
        assertEquals(OptionalLong.of(6), most(repeated(inTurn(AT_SIGN, AT_SIGN), 1, 3)));
        assertEquals(OptionalLong.of(0), most(repeated(AT_SIGN, 0, 0)));
    }

    @Test
    void aChoiceHoldsTheSignAsOftenAsItsMostHoldingArm() {
        assertEquals(OptionalLong.of(2), most(eitherOf(AT_SIGN, inTurn(AT_SIGN, AT_SIGN), LETTER)));
    }

    @Test
    void aPartNoStringSatisfiesDoesNotCountAndMakesNoStringOfWhatItIsPartOf() {
        assertEquals(OptionalLong.of(1), most(eitherOf(NEVER, AT_SIGN)));
        assertEquals(OptionalLong.of(0), most(inTurn(AT_SIGN, NEVER)));
        assertEquals(OptionalLong.of(0), most(repeated(NEVER, 1, NO_CEILING)));
        assertEquals(OptionalLong.of(0), most(repeated(NEVER, 0, NO_CEILING)));
    }

    @Test
    void aCeilingTooLargeForALongIsNoCeiling() {
        PatternMeaning once = repeated(AT_SIGN, 0, Integer.MAX_VALUE);
        assertEquals(OptionalLong.empty(), most(repeated(repeated(once, 0, Integer.MAX_VALUE), 0,
                Integer.MAX_VALUE)));
    }

    /** Every string up to six code points over a small alphabet, against the machine. */
    @Test
    void theCeilingIsWhatTheMachineAcceptsAndNeverLess() {
        List<PatternMeaning> patterns = List.of(
                inTurn(repeated(LETTER, 0, NO_CEILING), AT_SIGN, repeated(LETTER, 0, NO_CEILING)),
                inTurn(repeated(LETTER, 1, 3), AT_SIGN, repeated(LETTER, 1, 3)),
                eitherOf(AT_SIGN, inTurn(AT_SIGN, LETTER, AT_SIGN), LETTER),
                repeated(inTurn(LETTER, AT_SIGN), 0, 2),
                repeated(LETTER_OR_AT, 0, 4),
                inTurn(repeated(AT_SIGN, 0, 1), repeated(LETTER, 0, NO_CEILING)),
                eitherOf(NEVER, AT_SIGN));
        List<String> strings = stringsOver(List.of("a", "@", "b"), 6);
        for (PatternMeaning pattern : patterns) {
            long seen = 0;
            for (String each : strings) {
                if (Recognizer.recognizes(pattern, each).orElseThrow()) {
                    seen = Math.max(seen, each.chars().filter(c -> c == AT).count());
                }
            }
            OptionalLong most = most(pattern);
            assertTrue(most.isPresent(), pattern.toString());
            assertEquals(seen, most.getAsLong(), pattern.toString());
        }
    }

    private static List<String> stringsOver(List<String> alphabet, int longest) {
        List<String> out = new ArrayList<>();
        List<String> layer = List.of("");
        out.add("");
        for (int length = 1; length <= longest; length++) {
            List<String> next = new ArrayList<>();
            for (String prefix : layer) {
                for (String symbol : alphabet) {
                    next.add(prefix + symbol);
                }
            }
            out.addAll(next);
            layer = next;
        }
        return out;
    }
}
