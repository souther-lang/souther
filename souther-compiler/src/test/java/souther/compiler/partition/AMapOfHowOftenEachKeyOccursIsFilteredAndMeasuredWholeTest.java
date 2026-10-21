package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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
        assertTrue(offered.stream().anyMatch(each -> each.matches("\\[\"[^\"]*\"], 0"))
                        && offered.stream().anyMatch(each -> each.matches("\\[\"[^\"]*\"], 3")),
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

    /**
     * Keys a rule keeps from the empty string, as a label is kept to one letter at least: the key
     * written as often as a count asks is one its type admits, as the keys of a set of them are,
     * and not the first string along the order, which every row holding it is refused for. So
     * a row is offered on each side of the line, of a list of them or of the labels of a list of
     * issues alike.
     */
    @Test
    void aKeyWrittenAsOftenAsACountAsksIsOneItsTypeAdmits() {
        String labels = """
                module example.popular

                data Label = String
                    invariant String.length(value) >= 1

                """;
        String flat = labels + """
                let countsOf (xs: List<Label>): Map<String, Int> =
                    List.fold((acc, x) -> Map.updateOrInsert(x.value, 1, n -> n + 1, acc),
                        Map.empty, xs)

                behavior popular : (xs: List<Label>, atLeast: Int) -> Map<String, Int>

                let popular (xs, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(xs))
                """;
        String nested = labels + """
                data Issue = { id: String, labels: Set<Label> }

                let countsOf (issues: List<Issue>): Map<String, Int> =
                    List.fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty,
                        List.flatMap(i -> List.map(l -> l.value, Set.toList(i.labels)), issues))

                behavior popular : (issues: List<Issue>, atLeast: Int) -> Map<String, Int>

                let popular (issues, atLeast) =
                    Map.filterEntries((_, count) -> count >= atLeast, countsOf(issues))
                """;
        for (String model : List.of(flat, nested)) {
            Compilation compilation = measured(model);
            List<String> offered = offeredInputs(compilation);
            assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(compilation));
            assertTrue(offered.stream().noneMatch(each -> each.contains("Label(\"\")")),
                    () -> "no row holds a label the type refuses: " + offered);
            assertFalse(report(compilation).contains("nothing could show a row can be written"),
                    () -> "every point has a row composed for it: " + report(compilation));
        }
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
