package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a run may stop on the way to a comparison that reads a value defined by name is
 * whether what the value is defined as may end a run. Reading the value ends none; working out
 * its definition may, and that is asked of the definition.
 *
 * <p>One model, and only the definition of {@code floor} differs: the comparison on the way
 * reads it, and the one after it (line 12) is what is said not read where the reading of
 * {@code floor} is left unsaid.
 */
class AComparisonWhoseWayReadsAValueIsAskedOfTheValuesDefinitionTest {

    private static final String MODEL = """
            module e10

            data Limit = Int
                invariant value >= 0

            behavior f : (n: Int, on: Date, endsOn: Date) -> Bool

            let floor = %s

            let f (n, on, endsOn) =
                n < %s
                    && Date.daysBetween(on, endsOn) + 1 < 31
            """;

    private static final String THE_LATER_COMPARISON = "comparison@12:";

    @Test
    void aValueDefinedByAConstantIsReadWithoutEndingARun() {
        assertEquals(MeasurementStatus.COMPLETE,
                AdequacyReport.of(measured("31", "floor")).status());
    }

    @Test
    void aBuildOfADeclaredTypeIsReadWithoutEndingARunWhereItsInvariantHolds() {
        assertEquals(MeasurementStatus.COMPLETE,
                AdequacyReport.of(measured("Limit(31)", "floor.value")).status());
    }

    @Test
    void aValueWhoseDefinitionMayEndARunIsNotTakenToGetPast() {
        Compilation compilation = measured("Int.abs(9223372036854775807) + 1", "floor");
        AdequacyReport report = AdequacyReport.of(compilation);
        assertEquals(MeasurementStatus.PARTIAL, report.status());
        assertTrue(report.humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()))
                .lines().anyMatch(line -> line.contains("not read:")
                        && line.contains(THE_LATER_COMPARISON)));
    }

    private static Compilation measured(String definition, String compared) {
        return ACompiledModel.compiles(ACompiledModel.measured(
                MODEL.formatted(definition, compared),
                Adequacy.Asked.reportOnly(Adequacy.Level.OFF)));
    }
}
