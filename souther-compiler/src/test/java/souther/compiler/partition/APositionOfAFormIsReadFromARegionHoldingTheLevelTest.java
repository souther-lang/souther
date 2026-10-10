package souther.compiler.partition;

import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A position of a form is offered values out of a region that already holds the form at the level.
 *
 * <p>A gross that is a sum of several pay fields, an allowance capped by a ceiling, and a guard
 * holding the gross against what is subtracted from it. The lines of that sum are met by rows that
 * put the allowance at a small value, or put two fields at large values that move together, and
 * every position of the form is unbounded above.
 *
 * <p>Read from the region as it stood before the level was asked for, each field runs over the
 * whole of its range and the relation between the fields reaches the walk only as often as the
 * search is willing to pay for, so the walk is out of steps before it is at the row. Read from a
 * region that has the equation taken in, a field's run is already what the others leave it.
 */
class APositionOfAFormIsReadFromARegionHoldingTheLevelTest {

    private static final String A_CAPPED_ALLOWANCE = """
            module example.pay

            data Yen = Int
                invariant value >= 0

            data Pay =
                { base: Yen
                , scheduled: Yen
                , commuting: Yen
                , excluded: Yen
                , variable: Yen
                }

            data Over = { why: Int }
            data Amount = { v: Int }
            data Result = Over | Amount

            let total (p: Pay): Yen = p.base + p.scheduled + p.commuting + p.excluded + p.variable

            let exempt (p: Pay): Yen =
                if p.commuting > Yen(150000)
                then Yen(150000)
                else p.commuting

            behavior taxable : (pay: Pay, uplift: Yen, insurance: Yen) -> Result
                constructs Amount, Over, Yen

            let taxable (pay, uplift, insurance) = {
                let gross = total(pay) + uplift
                let subtracted = exempt(pay) + insurance
                guard gross >= subtracted else Over { why = 0 }
                Amount { v = gross.value - subtracted.value }
            }

            example taxable
                | "ordinary" :
                    (Pay { base = Yen(300000), scheduled = Yen(0), commuting = Yen(10000),
                           excluded = Yen(0), variable = Yen(0) }, Yen(0), Yen(40000))
                    -> Amount { v = 270000 }
            """;

    @Test
    void aLineOfASumOfSeveralFieldsIsNotLeftUntriedForTheStepsItWalked() {
        String report = report(A_CAPPED_ALLOWANCE);

        assertFalse(report.contains("this compiler stopped at"), report);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
