package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The searches for rows one behavior's lines are searched with stop at their figure
 * ({@link CompositionBudget#SEARCHES_FOR_ROWS_A_BEHAVIOR_MAKES}), and every point past it says that
 * figure stopped it: a point nobody searched is never read as one nothing can be written at.
 */
class TheSearchesOfABehaviorStopAtTheirFigureAndSaySoTest {

    private static final String MODULE = "example.searched";

    /** Two lines and no rows, so every point of both is searched, and far fewer than the figure. */
    private static final String FEW = """
            module example.searched

            behavior admit : (a: Int, b: Int) -> Bool
            let admit (a, b) = a <= 10 && b >= 3
            """;

    /**
     * As many lines as thresholds, and no rows: every point of every line is searched, and there
     * are more of them than the figure. A list of them, since a chain of that many is nested past
     * what a source may be.
     */
    private static String many(int thresholds) {
        return """
                module example.searched

                behavior admit : (a: Int) -> Bool
                let admit (a) = List.all(x -> x, [ %s ])
                """.formatted(IntStream.range(0, thresholds)
                .mapToObj(each -> "a > " + (each * 3))
                .collect(Collectors.joining(", ")));
    }

    /** What each point of the behavior's lines that a search was made at came to, in order. */
    private static List<SearchOutcomes> searchesOf(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        List<BorderAssessment> searched = compilation.db()
                .ask(new Adequacy.BoundarySearch(MODULE, "admit")).value();
        assertNotNull(searched, "the lines of admit were searched");
        List<SearchOutcomes> out = new ArrayList<>();
        for (BorderAssessment reading : searched) {
            for (ItemAssessment item : reading.items().values()) {
                if (item instanceof ItemAssessment.Owed owed && owed.searches().ran()) {
                    out.add(owed.searches());
                }
            }
        }
        assertFalse(out.isEmpty(), "some point of admit is searched");
        return out;
    }

    /** Whether the figure stopped every search at the point, and nothing else came of it. */
    private static boolean stoppedByTheFigure(SearchOutcomes searches) {
        return searches.each().stream().allMatch(each ->
                each instanceof ItemAssessment.Attempt.Stopped stopped
                        && stopped.stoppedBy().written().equals(
                                List.of(CompositionBudget.SEARCHES_FOR_ROWS_A_BEHAVIOR_MAKES)));
    }

    @Test
    void aBehaviorSearchedFewerTimesThanTheFigureIsStoppedNowhere() {
        searchesOf(FEW).forEach(searches -> assertFalse(stoppedByTheFigure(searches),
                searches::toString));
    }

    /**
     * The searches before the figure are made and every point after it says the figure stopped
     * it: once one is stopped, every one after it is.
     */
    @Test
    void pastTheFigureEveryPointSaysTheFigureStoppedIt() {
        int most = CompositionBudget.SEARCHES_FOR_ROWS_A_BEHAVIOR_MAKES.maximum();
        List<SearchOutcomes> searches = searchesOf(many(most / 2));
        int first = IntStream.range(0, searches.size())
                .filter(at -> stoppedByTheFigure(searches.get(at))).findFirst().orElse(-1);
        assertTrue(first > 0, "some searches are made and the figure stops the rest: "
                + searches.size() + " points searched");
        searches.subList(first, searches.size()).forEach(each ->
                assertTrue(stoppedByTheFigure(each), each::toString));
    }
}
