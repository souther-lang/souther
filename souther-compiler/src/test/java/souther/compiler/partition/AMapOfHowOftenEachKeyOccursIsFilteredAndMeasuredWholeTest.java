package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The keys of a list counted by a fold and the entries kept that occur often enough, measured from
 * the source to the rows: what the model states is read, the line it draws is owed a row on each
 * side, the rows offered for it are the ones that stand there, and the model written with them has
 * nothing left owed.
 */
class AMapOfHowOftenEachKeyOccursIsFilteredAndMeasuredWholeTest {

    private static final String MODEL = """
            module example.popular

            let countsOf (xs: List<String>): Map<String, Int> =
                List.fold((acc, x) -> Map.updateOrInsert(x, 1, n -> n + 1, acc), Map.empty, xs)

            behavior popular : (xs: List<String>, atLeast: Int) -> Map<String, Int>

            let popular (xs, atLeast) =
                Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))

            example popular
                | "one key often enough" : (["a", "a", "b"], 2) -> [("a", 2)]
                | "nothing counted" : ([], 2) -> []
            """;

    /**
     * The four rows the line is owed, written the way the offering writes them, and the rows that
     * tell it from every other line: a line through two quantities is told from the lines beside it
     * by rows at two different occurrences on each of its sides. The rows above stand at one
     * occurrence, and the example at two, so this adds the third at the line and the second just
     * short of it.
     */
    private static final String ANSWERED = """
                | "at the line" : ([""], 1) -> [("", 1)]
                | "one short of it" : ([""], 2) -> []
                | "well past it" : ([""], 0) -> [("", 1)]
                | "well short of it" : ([""], 3) -> []
                | "three alike" : (["a", "a", "a"], 3) -> [("a", 3)]
                | "two alike, a third wanted" : (["a", "a"], 3) -> []
            """;

    @Test
    void theModelDrawsItsLineAndIsOwedARowOnEachSideOfIt() {
        Compilation before = measured(MODEL);
        List<String> offered = offeredInputs(before);
        assertTrue(offered.contains("[\"\"], 0") && offered.contains("[\"\"], 3"),
                () -> "a row is offered past the line and one short of it: " + offered);
        assertTrue(report(before).contains("multiplicity(xs[*])"),
                () -> "the line is on how often a key occurs: " + report(before));
    }

    @Test
    void theModelWrittenWithThoseRowsHasNothingLeftOwed() {
        Compilation after = measured(MODEL + ANSWERED);
        assertEquals(List.of(), AdequacyReport.of(after).adequacyGaps().stream()
                        .map(each -> each.kind() + " " + each.about()).toList(),
                () -> "nothing is owed once the rows stand on the line: " + report(after));
    }

    private static List<String> offeredInputs(Compilation compilation) {
        return Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.popular"))
                .rowsByBehavior().getOrDefault("popular", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                "the source compiles");
        return compilation;
    }
}
