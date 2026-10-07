package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a map holds is read and written at the element, the way what a list holds is.
 *
 * <p>A body handed a map's values one at a time compares them as numbers of the input, so a line
 * drawn between one of them and a field beside it is owed rows on both sides. The whole way round:
 * the line is owed, a row is offered at each side of it, and writing those rows settles it.
 */
class AMapsValuesAreElementsOfTheInputTest {

    /** A body comparing what a map holds against the field beside it. */
    private static final String MODEL = """
            module example.popular

            data Usage = { counts: Map<String, Int>, atLeast: Int }

            behavior popular : (u: Usage) -> Map<String, Int>

            let popular (u) = Map.filterEntries((_, count) -> count >= u.atLeast, u.counts)

            example popular
                | "some" : (Usage { counts = [("a", 5), ("b", 1)], atLeast = 3 }) -> [("a", 5)]
                | "none" : (Usage { counts = [], atLeast = 3 }) -> []
            """;

    /** The rows the block offers for the two points the line is owed, answered. */
    private static final String ANSWERED = """
                | "on" : (Usage { counts = [("x", 0)], atLeast = 0 }) -> [("x", 0)]
                | "off" : (Usage { counts = [("x", -1)], atLeast = 0 }) -> []
            """;

    @Test
    void aLineOverAMapsValuesIsOwedOfferedAndThenMet() {
        Compilation before = measured(MODEL);

        List<String> unmet = unmetOf(before);
        assertEquals(2, unmet.size(), () -> "the line's two points are owed: " + report(before));

        String block = block(before);
        assertTrue(block.contains("counts = [(\"x\", 0)], atLeast = 0"),
                () -> "a row is offered on the line, as a map holding the value: " + block);
        assertTrue(block.contains("counts = [(\"x\", -1)], atLeast = 0"),
                () -> "and one beside it: " + block);

        Compilation after = measured(MODEL + ANSWERED);
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
        assertFalse(block(after).contains("counts = [(\"x\", 0)]"),
                () -> "and nothing is offered for it a second time: " + block(after));
    }

    private static List<String> unmetOf(Compilation compilation) {
        return AdequacyReport.of(compilation).adequacyGaps().stream()
                .filter(each -> each.kind() == Adequacy.Kind.BOUNDARY_UNMET)
                .map(each -> each.about().toString())
                .toList();
    }

    private static String block(Compilation compilation) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.popular")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
