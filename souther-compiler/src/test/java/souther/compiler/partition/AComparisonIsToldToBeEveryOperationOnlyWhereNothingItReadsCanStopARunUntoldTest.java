package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;

import java.util.Set;

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
        return told(body, "No");
    }

    private static UndividedByARelation.Working told(String body, String outcome) {
        String source = """
                module g

                data Yes
                data No

                behavior classify : (n: Int, m: Int, k: Int) -> Yes | No
                let classify (n, m, k) = %s

                %s
                """.formatted(body, outcome == null ? ""
                : "example classify\n    | \"one\" : (1, 1, 1) -> " + outcome);
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

    /**
     * An operation whose number does not move with the input is still one a run stops at: the
     * intermediate {@code 9223372036854775807 + 1} is past the type whatever {@code m} is, and
     * the number it comes to is told with no term in it.
     */
    @Test
    void anOperationThatReadsNoTermIsToldWithTheNumberItComesTo() {
        UndividedByARelation.Working working = told(
                "if (m - m) + 9223372036854775807 + 1 - 1 + n <= k then Yes else No",
                null);
        assertTrue(working.exact());
        UndividedByARelation.IntOperation past = working.operations().stream()
                .filter(each -> each.form().coefs().isEmpty())
                .filter(each -> each.form().constant().compareTo(
                        ExactRatio.of(each.greatest())) > 0)
                .findFirst().orElse(null);
        assertTrue(past != null, () -> "the sum past the greatest value is told: " + working);
    }

    /**
     * A comparison that was read but cuts no line, or whose difference no number holds, says
     * nothing of what the program works out. That is not that the program adds the form up, which
     * is what a row computed by the form's sizes assumes.
     */
    @Test
    void aComparisonThatDrewNoLineTellsNothingOfWhatTheProgramWorksOut() {
        assertEquals(UndividedByARelation.Working.UNREAD,
                AffineReading.OfAComparison.workingOf(new AffineReading.OfAComparison.CutsNothing(
                        Set.of(), ExactRatio.ZERO)));
        assertEquals(UndividedByARelation.Working.UNREAD,
                AffineReading.OfAComparison.workingOf(
                        new AffineReading.OfAComparison.NotHeld(Set.of())));
    }

    @Test
    void aProductOfTwoPositionsIsNotAFormAndIsNotToldToBeEveryOperation() {
        UndividedByARelation.Working working = told(
                "{\n    let p = n * m\n    if p + k >= 100 then Yes else No\n}");
        assertFalse(working != null && working.exact(),
                () -> "a product no form says is worked out and not told of: " + working);
    }
}
