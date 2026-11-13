package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.ArmObservation;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.report.AdequacyReport;
import souther.compiler.source.SourceId;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A membership after a sum that stops is not read as reached at every value, and the programs the
 * report says it of are run at the values on each side of the stop.
 *
 * <p>Each of the three programs of the issue stops at an {@code a} the form it states does not
 * show: the first two at 11, the third, which states {@code a - d}, at 1. A row one value short of
 * the stop is run and holds; a row at the stop is run and the body aborts. So the values the
 * report does not credit as witnesses are values no run gets past, and not a reading the programs
 * do not bear out.
 */
class TheValuesAProgramStopsAtAreTheOnesTheReportRefusesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String NOT_SHOWN = "relation_not_shown_to_reach_every_value";

    private static final String MEMBERSHIP = "Bool.not(Set.contains(a, hs))";

    private static final String MODEL = """
            module demo

            behavior sum : (a: Int, d: Int, hs: Set<Int>) -> Bool
            let sum (a, d, hs) = a + 9223372036854775797 - d >= 0 && MEMBERSHIP

            behavior remainder : (a: Int, d: Int, hs: Set<Int>) -> Bool
            let remainder (a, d, hs) = Int.floorMod(9223372036854775797 + a - d, 7) >= 1
                && MEMBERSHIP

            behavior cancelling : (a: Int, d: Int, hs: Set<Int>) -> Bool
            let cancelling (a, d, hs) =
                Int.floorMod(a + 9223372036854775807 - 9223372036854775807 - d, 7) >= 1
                && MEMBERSHIP

            example sum
                | "sum below the stop" : (10, 0, Set.empty) -> true
                | "sum at the stop" : (11, 0, Set.empty) -> true

            example remainder
                | "remainder below the stop" : (10, 1, Set.empty) -> true
                | "remainder at the stop" : (11, 1, Set.empty) -> true

            example cancelling
                | "cancelling below the stop" : (0, 1, Set.empty) -> true
                | "cancelling at the stop" : (1, 1, Set.empty) -> true
            """.replace("MEMBERSHIP", MEMBERSHIP);

    @Test
    void theRowsAtTheStopAbortAndTheRowsBelowItHold() {
        Compilation compilation = compiled();
        Map<String, RowOutcome> rows = new java.util.LinkedHashMap<>();
        SourceId source = compilation.exampleSourcesOf("demo").getFirst();
        for (RowOutcome row : compilation.db()
                .ask(new Output.Examples("demo", source, ArmObservation.OMIT)).value().rows()) {
            rows.put(row.identity().shown(), row);
        }
        assertEquals(6, rows.size(), rows::toString);
        for (String program : List.of("sum", "remainder", "cancelling")) {
            RowOutcome below = rows.get(program + " below the stop");
            RowOutcome at = rows.get(program + " at the stop");
            assertEquals(Disposition.HELD, below.disposition(), program);
            assertEquals(Disposition.FAILED, at.disposition(), program);
            assertEquals(FailurePhase.INVOCATION, at.failurePhase(), program);
        }
    }

    @Test
    void theMembershipOfNoneOfThemIsShownReachedAtEveryValue() {
        JsonNode report = JSON.readTree(AdequacyReport.of(compiled())
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        for (String program : List.of("sum", "remainder", "cancelling")) {
            Set<String> found = new TreeSet<>();
            collect(report, program, found);
            assertEquals(Set.of(NOT_SHOWN), found, program);
        }
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        // The row at each stop says the body answers, and it aborts: a row that disagrees with the
        // model is refused at compile time, and these three are the only refusals.
        return ACompiledModel.refusedWith(List.of("E1905", "E1905", "E1905"), compilation);
    }

    private static void collect(JsonNode node, String behavior, Set<String> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason")
                && node.path("position").asString().equals("hs[*]")
                && node.path("ruleId").path("behavior").asString().equals(behavior)) {
            out.add(node.path("reason").asString());
        }
        node.forEach(child -> collect(child, behavior, out));
    }
}
