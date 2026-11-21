package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison whose way reads a value defined by name is not read for that reason only where the
 * value's definition can end a run. Reading the value ends none; what it is defined as may, and
 * that is asked of the definition.
 *
 * <p>The comparison on the way to the later one reads {@code floor}, and the later one is what
 * is said not read when the reading of {@code floor} is left unsaid.
 */
class AComparisonWhoseWayReadsAValueIsAskedOfTheValuesDefinitionTest {

    private static final String MODEL = """
            module e10

            data Hours = Decimal
                invariant value >= 0.0m

            behavior f : (hours: Hours, on: Date, endsOn: Date) -> Bool

            %s

            let f (hours, on, endsOn) =
                hours.value < %s && Date.daysBetween(on, endsOn) + 1 < %s
            """;

    @Test
    void aValueDefinedByAConstantEndsNoRunWhenItIsRead() {
        assertFalse(notRead(MODEL.formatted("let floor = 20.0m", "floor", "31")));
    }

    @Test
    void aBuildOfADeclaredTypeEndsNoRunWhenItsInvariantHolds() {
        assertFalse(notRead(MODEL.formatted("let floor = Hours(20.0m)", "floor.value", "31")));
    }

    @Test
    void aValueWhoseDefinitionMayEndARunIsNotTakenToGetPast() {
        assertTrue(notRead("""
                module e10

                behavior f : (n: Int, on: Date, endsOn: Date) -> Bool

                let floor = Int.abs(9223372036854775807) + 1

                let f (n, on, endsOn) =
                    n < floor
                        && Date.daysBetween(on, endsOn) + 1 < 31
                """, "comparison@9:"));
    }

    private static boolean notRead(String model) {
        return notRead(model, "");
    }

    /** Whether the report says what was not read at {@code where}, or anywhere for the empty
     *  one. */
    private static boolean notRead(String model, String where) {
        Compilation compilation = ACompiledModel.compiles(ACompiledModel.measured(model,
                Adequacy.Asked.reportOnly(Adequacy.Level.OFF)));
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .anyMatch(line -> line.contains("not read:") && line.contains(where));
    }
}
