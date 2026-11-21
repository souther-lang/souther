package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison whose way reads a value defined by name is said to be one a run may stop on the way
 * to only where the value's definition can end a run. Reading the value ends none; working out
 * what it is defined as may, and that is asked of the definition.
 */
class AComparisonWhoseWayReadsAValueIsAskedOfTheValuesDefinitionTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module e10

            data Hours = Decimal
                invariant value >= 0.0m

            data TermUntil = { endsOn: Date }
            data ContractTerm = Indefinite | TermUntil

            data Few = { hours: Hours }
            data Short = { endsOn: Date }
            data Reason = Few | Short

            behavior exclusions : (hours: Hours, contract: ContractTerm, on: Date) -> List<Reason>

            %s

            let contractEnd (contract: ContractTerm, on: Date): List<Date> =
                match contract with
                    | Indefinite           -> []
                    | TermUntil { endsOn } -> [ endsOn | Date.daysBetween(on, endsOn) + 1 < %s ]

            let exclusions (hours, contract, on) =
                [ Few { hours = hours } | %s ]
                  ++ List.map(d -> Short { endsOn = d }, contractEnd(contract, on))
            """;

    @Test
    void aDecimalDefinedByNameEndsNoRunWhenItIsRead() {
        assertEquals(List.of(), mayStop("let floor = 20.0m", "hours.value < floor"));
    }

    @Test
    void aBuildWithAnInvariantTheValueHoldsEndsNoRunWhenItIsRead() {
        assertEquals(List.of(),
                mayStop("let floor = Hours(20.0m)", "hours.value < floor.value"));
    }

    @Test
    void aValueDefinedByAnotherValueEndsNoRunWhenItIsRead() {
        assertEquals(List.of(), mayStop("""
                let base = 20.0m
                let floor = base""", "hours.value < floor"));
    }

    @Test
    void aValueWhoseDefinitionEndsARunIsNotTakenToGetPast() {
        List<String> lines = mayStop("let floor = Int.abs(9223372036854775807) + 1",
                "hours.value < 20.0m", "floor");
        assertTrue(!lines.isEmpty(), "a definition that may end a run is not taken past");
    }

    private static List<String> mayStop(String values, String condition) {
        return mayStop(values, condition, "31");
    }

    /** The lines of the report saying what was not read. */
    private static List<String> mayStop(String values, String condition, String days) {
        Compilation compilation = measured(MODEL.formatted(values, days, condition));
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:"))
                .toList();
    }

    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static Compilation measured(String model) {
        Compilation shared = MEASURED.computeIfAbsent(model,
                source -> ACompiledModel.measured(source, Adequacy.Asked.fullReport()));
        return ACompiledModel.compiles(shared);
    }
}
