package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison inside a closure, one side of which is a total over the elements a filter keeps,
 * is read in the ways the elements are kept once for all the applications of the closure: the
 * total is the same on each of them, and only the constant it is compared with differs.
 */
class AComparisonInAClosureIsReadOnceForTheWaysOfATotalThatDoesNotTurnOnTheElementTest {

    private static final String PREAMBLE = """
            module p
            data Month = { pay: Int, days: Int }
            data Window = { first: Month, second: Month, third: Month, fourth: Month }
            data Ok
            data No
            """;

    private static String report(String body) {
        Compilation compilation = Compilation.ofSource(PREAMBLE + body, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("\\d+:\\d+", "");
    }

    private static String table(int rows) {
        return IntStream.rangeClosed(1, rows).mapToObj(Integer::toString)
                .collect(Collectors.joining(", ", "[ ", " ]"));
    }

    private static String reachedBy(String applied, int rows) {
        return report("""
                behavior g : (w: Window) -> Ok | No
                let g (w) = {
                    guard List.any(t -> t <= %s, %s) else No
                    Ok
                }
                """.formatted(applied, table(rows)));
    }

    private static final String MEAN = """
            List.length(List.filter(r -> r.days >= 17,
                [ w.first, w.second, w.third, w.fourth ]))""";

    /** The ways four months are each kept or dropped in. */
    private static final int WAYS = 16;

    @Test
    void aTableWalkedAgainstAFilteredTotalIsReadWhateverItsLength() {
        int rows = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / WAYS + 1;
        String report = reachedBy(MEAN, rows);
        assertFalse(report.contains("READINGS_OF_ONE_CONDITION"), report);
        assertTrue(report.contains("read as g/w.first.days"), report);
    }

    /**
     * A table short enough to have been read before is drawn the same lines when it is longer than
     * the figure allowed it to be.
     */
    @Test
    void aLongTableDrawsTheLinesAShortOneDoes() {
        int rows = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / WAYS + 1;
        Set<String> long_ = linesOn(reachedBy(MEAN, rows));
        for (int shorter : new int[] {1, 2, 8}) {
            Set<String> drawn = linesOn(reachedBy(MEAN, shorter));
            assertFalse(drawn.isEmpty(), "rows " + shorter);
            Set<String> missing = new TreeSet<>(drawn);
            missing.removeAll(long_);
            assertEquals(Set.of(), missing, "rows " + shorter);
        }
    }

    private static Set<String> linesOn(String report) {
        return report.lines().filter(line -> line.contains("read as"))
                .map(line -> line.strip().replaceFirst(" — .*", ""))
                .collect(Collectors.toSet());
    }

    /** A total whose ways turn on the constant of the application is another total on each. */
    @Test
    void aTotalWhoseKeepingTurnsOnTheApplicationIsStillStoppedByTheFigure() {
        int rows = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum() / WAYS + 1;
        String report = report("""
                behavior g : (w: Window) -> Ok | No
                let g (w) = {
                    guard List.any(t -> t <= List.sum(List.map(r -> r.pay,
                        List.filter(r -> r.days >= t, [ w.first, w.second, w.third, w.fourth ]))),
                        %s) else No
                    Ok
                }
                """.formatted(table(rows)));
        assertTrue(report.contains("READINGS_OF_ONE_CONDITION"), report);
    }
}
