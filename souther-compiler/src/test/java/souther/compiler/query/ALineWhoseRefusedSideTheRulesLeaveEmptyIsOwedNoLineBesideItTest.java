package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line whose refused side the model's own rules leave empty is owed no row ruling out a line
 * beside it, and the lines are said to be that rather than left out.
 *
 * <p>Ruling a line of the family out takes a row the model refuses, or one it keeps past a row it
 * refuses. Beyond an invariant's bound neither can be constructed, and given only rows the model
 * keeps, a threshold past every one of them keeps them all — so no number of rows settles the
 * question, and asking it would hold every model with such a rule open for ever.
 *
 * <p>With a control. The same relation written as a guard of the body has a refused side rows can
 * stand on, and there the lines are put to the rows like any other: what decides is the proof that
 * the rules refuse the far side, and not the shape of the relation.
 */
class ALineWhoseRefusedSideTheRulesLeaveEmptyIsOwedNoLineBesideItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** {@code low <= high} kept by the record's invariant, and so by construction. */
    private static final String HELD_BY_THE_INVARIANT = """
            module example.range

            data Range = { low: Int, high: Int }
                invariant low <= high

            behavior width : (r: Range) -> Int
            let width (r) = r.high - r.low

            example width
              | (Range { low = 1, high = 2 }) -> 1
              | (Range { low = 0, high = 0 }) -> 0
            """;

    /** The same relation, held by a guard the rows can stand on either side of. */
    private static final String HELD_BY_A_GUARD = """
            module example.range

            behavior width : (low: Int, high: Int) -> Int
            let width (low, high) = {
                guard low <= high else 0
                high - low
            }

            example width
              | (1, 2)  -> 1
              | (0, 0)  -> 0
              | (0, 1)  -> 1
              | (1, 0)  -> 0
              | (5, -5) -> 0
            """;

    @Test
    void everyLineBesideAnInvariantsBoundIsNotApplicable() {
        Set<String> standing = standingBeside(HELD_BY_THE_INVARIANT, "low");
        assertEquals(Set.of("not_applicable"), standing,
                "the family is said, and none of it is owed a row");
        assertTrue(report(HELD_BY_THE_INVARIANT).contains("adequacy: satisfied"),
                () -> "and it holds no verdict open:\n" + report(HELD_BY_THE_INVARIANT));
    }

    @Test
    void theSameRelationAsAGuardIsPutToTheRows() {
        Set<String> standing = standingBeside(HELD_BY_A_GUARD, "low");
        assertFalse(standing.isEmpty(), "the guard's line has a family");
        assertFalse(standing.contains("not_applicable"),
                () -> "rows stand on both sides of a guard, so its lines are asked about: "
                        + standing);
    }

    /** Where each line of the family stands, over every boundary whose axis names {@code at}. */
    private static Set<String> standingBeside(String model, String at) {
        Set<String> out = new TreeSet<>();
        for (JsonNode boundary : boundaries(document(model))) {
            if (!boundary.path("axis").asString().contains(at)) {
                continue;
            }
            for (JsonNode beside : boundary.get("besides")) {
                out.add(beside.get("standing").asString());
            }
        }
        return out;
    }

    private static List<JsonNode> boundaries(JsonNode document) {
        List<JsonNode> out = new ArrayList<>();
        collect(document, out);
        return out;
    }

    /** Every object holding a {@code besides} array, wherever the document puts it. */
    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("besides")) {
            out.add(node);
        }
        for (JsonNode child : node) {
            collect(child, out);
        }
    }

    private static JsonNode document(String model) {
        Compilation compilation = measured(model);
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }

    private static String report(String model) {
        Compilation compilation = measured(model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
