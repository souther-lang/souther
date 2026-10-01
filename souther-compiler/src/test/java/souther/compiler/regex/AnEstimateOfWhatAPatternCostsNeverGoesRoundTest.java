package souther.compiler.regex;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternMeaning;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a pattern is estimated to cost climbs and stops, and never comes back round.
 *
 * <p>The number decides which of several plans is worked out first, so it is compared. A count that
 * overflowed would put a repetition of a repetition below a single symbol, and the comparison would
 * not be an order at all — two plans could each come before the other, and which one was built first
 * would be the sort's business rather than the plan's.
 *
 * <p>Nothing is claimed about how close it is. It is read off the shape of the pattern and the real
 * machine is usually smaller; what it is for is putting the plainly small ones first, and being
 * wrong costs states rather than answers.
 */
class AnEstimateOfWhatAPatternCostsNeverGoesRoundTest {

    private static long states(String regex) {
        PatternRead said = PatternParser.read(regex);
        return PatternPlan.of(assertInstanceOf(PatternRead.Read.class, said, regex).meaning())
                .states();
    }

    /** A symbol is one state, and what is written out of copies is that many. */
    @Test
    void whatIsWrittenOutOfCopiesCostsThatMany() {
        assertEquals(1, states("a"));
        assertTrue(states("a{300}") > states("a"), "three hundred copies is more than one");
        assertTrue(states("x|a{300}") > states("x"), "and an arm of a choice is in what it costs");
    }

    /**
     * And a repetition of a repetition of a repetition stops climbing.
     *
     * <p>Each of these multiplies the last, so counted without a ceiling the fourth would pass what
     * a whole number holds and come back as something small or negative. The reader admits no such
     * pattern, so the meaning is put together as a caller of a plan may put one together.
     */
    @Test
    void anEstimateThatWouldPassEveryNumberStopsAtOne() {
        long deep = PatternPlan.of(fourTimesOver('a')).states();
        assertTrue(deep > 0, "it does not come back round: " + deep);
        assertEquals(deep, PatternPlan.of(fourTimesOver('b')).states(),
                "and every pattern past the ceiling is at the ceiling");
        assertTrue(deep > states("a{300}"), "which is still above what is merely large");
    }

    /** {@code (((c{60000}){60000}){60000}){60000}}, as what it means. */
    private static PatternMeaning fourTimesOver(char c) {
        PatternMeaning out = new PatternMeaning.Symbols(CodePoints.of(c));
        for (int i = 0; i < 4; i++) {
            out = new PatternMeaning.Repeated(out, 60_000, 60_000);
        }
        return out;
    }
}
