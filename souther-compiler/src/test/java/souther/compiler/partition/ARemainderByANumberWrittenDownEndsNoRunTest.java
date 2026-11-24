package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.StatedComparison;
import souther.compiler.inputs.Denotation;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A floor remainder ends a run only where what it divides by is nought, so one by a number that
 * folds to another ends none, whatever it divides. By nought, folded so or not, and by a number
 * the input holds, it may.
 */
class ARemainderByANumberWrittenDownEndsNoRunTest {

    /** Whether working out the left side of {@code condition}, over {@code n}, {@code m} and
     *  {@code k}, ends no run. */
    private static boolean theLeftSideEndsNoRun(String condition) {
        ReadComparisons read = ReadComparisons.ofTheAnalysis("""
                module w1
                behavior m : (n: Int, m: Int, k: Int) -> Bool
                let m (n, m, k) = %s
                """.formatted(condition), "m");
        ComparisonReadings.Reading only = read.only();
        StatedComparison stated =
                ((ComparisonReadings.Stated.AComparison) only.statement()).comparison();
        return WorkedOutToReachIt.of(read.inputs().reading(read.rules()))
                .endsNoRun(new Denotation(stated.left(), only.reads()));
    }

    @Test
    void byANumberWrittenDownOtherThanNoughtItEndsNone() {
        assertTrue(theLeftSideEndsNoRun("Int.floorMod(n, 7) >= k"));
        assertTrue(theLeftSideEndsNoRun("Int.floorMod(n, 0 - 7) >= k"));
    }

    @Test
    void byNoughtItMay() {
        assertFalse(theLeftSideEndsNoRun("Int.floorMod(n, 0) >= k"));
        assertFalse(theLeftSideEndsNoRun("Int.floorMod(n, 7 - 7) >= k"));
    }

    @Test
    void byANumberTheInputHoldsItMay() {
        assertFalse(theLeftSideEndsNoRun("Int.floorMod(n, m) >= k"));
    }
}
