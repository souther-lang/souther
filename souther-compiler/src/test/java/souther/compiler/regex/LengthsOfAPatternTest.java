package souther.compiler.regex;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternMeaning;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The fewest and the most code points a string a pattern accepts holds, read off the pattern, are
 * what the machine of the pattern says of the same strings.
 */
class LengthsOfAPatternTest {

    private static final Meter ROOMY = new Meter(100_000, 10_000_000, 1_000_000_000L);

    private static final PatternMeaning DIGIT = new PatternMeaning.Symbols(CodePoints.DIGITS);
    private static final PatternMeaning NO_SYMBOL = new PatternMeaning.Symbols(CodePoints.NONE);
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

    /** What the machine of {@code meaning} says, which is what this has to come to wherever no
     *  length passes what a string holds. */
    private static LengthsOfAPattern.Bounds machine(PatternMeaning meaning) {
        Language.Ends ends = PatternPlan.of(meaning).compile(ROOMY).lengths();
        return ends == null ? null : new LengthsOfAPattern.Bounds(ends.least(), ends.most());
    }

    @Test
    void eachShapeOfAPatternIsReadAsItsMachineReadsIt() {
        List<PatternMeaning> patterns = List.of(
                NOTHING,
                DIGIT,
                inTurn(DIGIT, DIGIT, DIGIT),
                repeated(DIGIT, 2, 4),
                repeated(DIGIT, 0, PatternMeaning.Repeated.NO_CEILING),
                repeated(DIGIT, 1, PatternMeaning.Repeated.NO_CEILING),
                repeated(NOTHING, 3, PatternMeaning.Repeated.NO_CEILING),
                repeated(repeated(DIGIT, 2, 3), 2, 2),
                eitherOf(inTurn(DIGIT, DIGIT, DIGIT), repeated(DIGIT, 5, 5)),
                eitherOf(NOTHING, DIGIT),
                eitherOf(NEVER, DIGIT),
                inTurn(DIGIT, repeated(DIGIT, 0, 2), NOTHING),
                repeated(NEVER, 0, 3));
        for (PatternMeaning pattern : patterns) {
            assertEquals(machine(pattern), LengthsOfAPattern.of(pattern), pattern.toString());
        }
    }

    @Test
    void aPatternNothingSatisfiesAcceptsNoString() {
        for (PatternMeaning pattern : List.of(NEVER, NO_SYMBOL, inTurn(DIGIT, NEVER),
                repeated(NEVER, 1, 3), eitherOf(NEVER, NO_SYMBOL))) {
            assertNull(LengthsOfAPattern.of(pattern), pattern.toString());
            assertNull(machine(pattern), "the machine agrees: " + pattern);
        }
    }

    @Test
    void theEmptyStringIsAcceptedWhereTheFewestIsNought() {
        assertEquals(0, LengthsOfAPattern.of(repeated(DIGIT, 0, 5)).least());
        assertEquals(0, LengthsOfAPattern.of(eitherOf(NOTHING, DIGIT)).least());
        assertEquals(1, LengthsOfAPattern.of(inTurn(repeated(DIGIT, 0, 5), DIGIT)).least());
    }

    @Test
    void aLengthPastWhatAStringHoldsIsNoCeilingAndTheFewestStaysBelowIt() {
        PatternMeaning huge = repeated(repeated(DIGIT, 1_000_000, 1_000_000), 1_000_000,
                1_000_000);
        LengthsOfAPattern.Bounds ends = LengthsOfAPattern.of(huge);
        assertNull(ends.most(), "a ceiling no string reaches is none");
        assertEquals(true, ends.least() > 0 && ends.least() < Long.MAX_VALUE / 2,
                "and the fewest does not wrap: " + ends);
    }
}
