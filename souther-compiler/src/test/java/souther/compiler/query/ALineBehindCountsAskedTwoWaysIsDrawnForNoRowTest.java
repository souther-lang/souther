package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.partition.Level;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line behind a condition every way of which asks how many elements meet a statement for a
 * count the way before it already leaves none of is reached by no row, and is drawn for none.
 *
 * <p>{@code List.any(x -> x > 5, xs)} leaves one or more elements above five, and each way of the
 * condition after it asks for none. That is said in the words of what closed the first way — a count
 * asked to be two things at once — as a case or a truth asked twice is, and not passed over as a
 * way some row takes with the other conditions on it left out. A way with nothing of several ways
 * on it asking the same two counts is closed the same way.
 */
class ALineBehindCountsAskedTwoWaysIsDrawnForNoRowTest {

    private static final String SOURCE = """
            module probe.closed

            data N = Int
                invariant value >= 0 && value <= 100

            data Yes
            data No

            behavior f : (xs: List<N>, n: N) -> Yes | No

            let f (xs, n) = {
                guard List.any(x -> x > 5, xs) else No
                guard List.all(x -> x <= 5, xs) || (n > 7 && List.all(x -> x <= 5, xs)) else No
                if n > 50 then Yes else No
            }

            example f
                | "none above" : ([ N(1) ], N(3)) -> No
            """;

    /** The same counts asked on a way with nothing of several ways on it, which is closed for the
     *  same reason and by the same judge. */
    private static final String ONE_WAY = SOURCE.replace(
            "guard List.all(x -> x <= 5, xs) || (n > 7 && List.all(x -> x <= 5, xs)) else No",
            "guard List.all(x -> x <= 5, xs) else No");

    private static final Count BEHIND_THE_CONDITIONS = Count.of(50);

    @Test
    void theLineBehindTheConditionsIsDrawnForNoRow() {
        drawnForNoRow(SOURCE);
    }

    @Test
    void theLineBehindCountsAskedTwiceOnOneWayIsDrawnForNoRow() {
        assertNotEquals(SOURCE, ONE_WAY, "the condition of several ways is taken away");
        drawnForNoRow(ONE_WAY);
    }

    private static void drawnForNoRow(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<BorderAssessment> edges = compilation.db()
                .ask(new Adequacy.BoundarySearch("probe.closed", "f")).value();
        assertNotNull(edges, "the lines of this behavior were searched");
        assertTrue(edges.stream().noneMatch(each ->
                        each.border().origin().comparisonAt().isPresent()
                                && each.border().cut().at()
                                        instanceof Level.OnACarrier(_, var at)
                                && at instanceof Count count
                                && count.compareTo(BEHIND_THE_CONDITIONS) == 0),
                () -> "no line is drawn where no row arrives: " + edges.stream()
                        .map(each -> each.border().obligation().toString()).toList());
    }
}
