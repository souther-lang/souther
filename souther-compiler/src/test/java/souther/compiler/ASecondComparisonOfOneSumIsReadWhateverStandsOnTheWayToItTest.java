package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two comparisons of one sum are read whether the range of a term comes from its type or from a
 * guard on the way, and whichever of them is asked first.
 *
 * <p>The comparison asked second stands under the statement that the first one failed, which is
 * {@code a + b <= 50} under {@code a + b < 50}. That statement holds at 49 and at 50, the two
 * values {@code a + b < 50} changes between, so it leaves the sides as they stand to one another
 * there and ties neither to the other. Asked at 51 as well, where it fails, it was kept as a tie,
 * and a guard on one term (which the declarations do not state) was then a range no reading of
 * the comparison reached.
 */
class ASecondComparisonOfOneSumIsReadWhateverStandsOnTheWayToItTest {

    private static final String MODEL = """
            module m

            data A = Int
                invariant value >= 0 && value <= 49

            data B = Int
                invariant value >= 0 && value <= 12

            data B1 = Int
                invariant value >= 1 && value <= 12

            behavior guardedAbove : (a: A, b: B) -> Int
            let guardedAbove (a, b) =
                if b.value >= 1 then
                    if a.value + b.value > 50 then 1
                    else if a.value + b.value < 50 then 2
                    else 3
                else 0

            behavior declaredAbove : (a: A, b: B1) -> Int
            let declaredAbove (a, b) =
                if a.value + b.value > 50 then 1
                else if a.value + b.value < 50 then 2
                else 3

            behavior unguardedAbove : (a: A, b: B) -> Int
            let unguardedAbove (a, b) =
                if a.value + b.value > 50 then 1
                else if a.value + b.value < 50 then 2
                else 3

            behavior unguardedBelow : (a: A, b: B) -> Int
            let unguardedBelow (a, b) =
                if a.value + b.value < 50 then 2
                else if a.value + b.value > 50 then 1
                else 3

            behavior guardedBelow : (a: A, b: B) -> Int
            let guardedBelow (a, b) =
                if b.value >= 1 then
                    if a.value + b.value < 50 then 2
                    else if a.value + b.value > 50 then 1
                    else 3
                else 0

            behavior guardedOnce : (a: A, b: B) -> Int
            let guardedOnce (a, b) =
                if b.value >= 1 then
                    if a.value + b.value < 50 then 2 else 3
                else 0

            behavior guardedAtMostOrAtLeast : (a: A, b: B) -> Int
            let guardedAtMostOrAtLeast (a, b) =
                if b.value >= 1 then
                    if a.value + b.value >= 50 then 1
                    else if a.value + b.value <= 49 then 2
                    else 3
                else 0
            """;

    private static String measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Each of the behaviors measured on its own, so that a refusal is named to its behavior. */
    @Test
    void everyOrderOfTheTwoComparisonsIsReadWithAGuardOnOneTermOrWithout() {
        String human = measured(MODEL);

        assertTrue(human.contains("measurement: complete"), human);
        assertFalse(human.contains("not read"), human);
    }

    /**
     * The statement the first comparison leaves behind leaves room at the line only for numbers
     * that move in whole steps. A {@code Decimal} sum takes the values between 49 and 50, so the
     * statement {@code s <= 50} is still a tie there, and the second comparison is not read.
     */
    @Test
    void aSumOfDecimalsIsStillAskedAStepEitherSideOfTheLine() {
        String human = measured("""
                module m

                data A = Decimal
                    invariant value >= 0 && value <= 49

                data B = Decimal
                    invariant value >= 0 && value <= 12

                behavior f : (a: A, b: B) -> Int
                let f (a, b) =
                    if b.value >= 1 then
                        if a.value + b.value > 50 then 1
                        else if a.value + b.value < 50 then 2
                        else 3
                    else 0
                """);

        assertTrue(human.contains("not read"), human);
    }
}
