package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meaning.CaseExpansion;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A helper is named beside a line only where the line was read all the same although its cases
 * were more ways of choosing one than are taken apart, and its cases are shown to choose among
 * the helper's readings one beside another ({@link CaseExpansion.Counted#costly}).
 *
 * <p>What this holds is where it is not said: a line not worked out is told of as it always was,
 * with no entry beside it for a line read at a cost, and a line whose cases are within the figure
 * has none.
 */
class AHelperIsNamedWhereALineWasReadAtACostTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module demo exposing (g)
            let ok (x: Int, y: Int, t: Int): Bool = x > t && y > t && x + y > t
            let first (x: Int, y: Int, step: Int): Int =
                Option.withDefault(0, List.find(t -> ok(x, y, t * step), [1, 2, 3, 4, 5, 6, 7]))
            let pick (x: Int, y: Int): Int = if x > y then first(x, y, 1) else first(y, x, 2)
            behavior g : (x: Int, y: Int) -> Bool
            let g (x, y) = pick(x, y) > 3
            """;

    private static JsonNode partition(int figure) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main").allowing(
                Allowances.DECLARED.with(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO,
                        figure));
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        ACompiledModel.compiles(compilation);
        return JSON.readTree(AdequacyReport.of(compilation)
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .path("modules").get(0).path("behaviors").get(0).path("partition");
    }

    @Test
    void aLineNotWorkedOutHasNoEntryBesideItForALineReadAtACost() {
        JsonNode partition = partition(0);
        assertFalse(partition.path("caseExpansions").isEmpty(),
                "the line is not worked out, and its cases are told of: " + partition);
        assertFalse(partition.has("costlyReadings"), partition.toString());
    }

    @Test
    void aLineWhoseCasesAreWithinTheFigureIsToldOfNothing() {
        JsonNode partition = partition(1000);
        assertTrue(partition.path("caseExpansions").isEmpty(), partition.toString());
        assertFalse(partition.has("costlyReadings"), partition.toString());
    }
}
