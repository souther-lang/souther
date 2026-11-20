package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.DateTranslation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import java.time.LocalDate;
import java.util.BitSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The search for years tells what it does not look at by what could hold the statements, and not
 * by whether it found anything: a year of one date held between two others, with every year it
 * looks at made nothing of, is looked at whole where the interval is short and not where it is
 * long, whatever a later search would find there.
 */
class TheYearsSearchTellsWhatItDoesNotLookAtTest {

    private static boolean everyYearLookedAtBetween(long first, long last) {
        YearsAWayAllows.Year year = new YearsAWayAllows.Year(0, ExactRatio.ONE,
                DateTranslation.none());
        BitSet everyYearOfTheCycle = new BitSet(PartsOfADateOverACycle.YEARS_OF_A_CYCLE);
        everyYearOfTheCycle.set(0, PartsOfADateOverACycle.YEARS_OF_A_CYCLE);
        YearsAWayAllows.Looked looked = new YearsAWayAllows.Looked();
        YearsAWayAllows.holding(List.of(
                        new YearsAWayAllows.Statement(List.of(year), ExactRatio.of(-first),
                                Rel.GE),
                        new YearsAWayAllows.Statement(List.of(year), ExactRatio.of(-last),
                                Rel.LE)),
                List.of(everyYearOfTheCycle),
                List.of(new int[] {LocalDate.MIN.getYear(), LocalDate.MAX.getYear()}),
                _ -> null, looked);
        return looked.everything();
    }

    @Test
    void aShortIntervalIsLookedAtWhole() {
        assertTrue(everyYearLookedAtBetween(1900, 1950));
    }

    @Test
    void aLongIntervalIsNotSaidToBeLookedAtWhole() {
        assertFalse(everyYearLookedAtBetween(3000, 100_000));
    }
}
