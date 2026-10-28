package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a comparison works out is told as every operation a run can stop at only where nothing the
 * reading went through can stop a run without telling of it: a row is computed, on that, where
 * each operation told holds at it, and a number worked out and not told of would make it computed
 * where it is not.
 */
class AComparisonIsToldToBeEveryOperationOnlyWhereNothingItReadsCanStopARunUntoldTest {

    /** What reading the comparison of {@code body} told, or null where the reading stopped. */
    private static UndividedByARelation.Working told(String body) {
        String source = """
                module g

                data Yes
                data No

                behavior classify : (n: Int, m: Int, k: Int) -> Yes | No
                let classify (n, m, k) = %s

                example classify
                    | "one" : (1, 1, 1) -> No
                """.formatted(body);
        ReadComparisons read = ReadComparisons.of(source, "classify");
        ComparisonReadings.Reading against = read.only();
        return AffineReading.read(
                ((ComparisonReadings.Stated.AComparison) against.statement()).comparison(),
                against.reads(), read.inputs().reading(read.rules()))
                instanceof AffineReading.OfAComparison.Cuts cuts ? cuts.working() : null;
    }

    @Test
    void sumsOfThePositionsOfTheInputAreEveryOperation() {
        UndividedByARelation.Working working = told("if n + m + k >= 100 then Yes else No");
        assertTrue(working.exact());
        assertEquals(2, working.operations().size());
    }

    @Test
    void aSumKeptUnderANameIsToldWhereItIsRead() {
        UndividedByARelation.Working working = told(
                "{\n    let s = n + m\n    if s + k >= 100 then Yes else No\n}");
        assertTrue(working.exact());
        assertEquals(2, working.operations().size());
    }

    @Test
    void aProductOfTwoPositionsIsNotAFormAndIsNotToldToBeEveryOperation() {
        UndividedByARelation.Working working = told(
                "{\n    let p = n * m\n    if p + k >= 100 then Yes else No\n}");
        assertFalse(working != null && working.exact(),
                () -> "a product no form says is worked out and not told of: " + working);
    }
}
