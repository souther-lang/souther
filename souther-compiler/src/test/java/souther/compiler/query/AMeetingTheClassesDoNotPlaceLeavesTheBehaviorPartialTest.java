package souther.compiler.query;

import souther.compiler.ACompiledModel;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A meeting whose combinations the classes of the input do not place is asked for over a wider
 * region, and the behavior says which of its combinations nothing made and nothing showed to exist.
 *
 * <p>The first operand below is a relation between two positions, which no class of either states.
 * So its outcomes narrow no position, and no cell steers a row into one of the meeting's
 * combinations rather than another. The combinations are still owed: a row is credited with one by
 * what its run did, and one nothing made is not shown to exist by the classes.
 */
class AMeetingTheClassesDoNotPlaceLeavesTheBehaviorPartialTest {

    private static final String MODEL = """
            module example.fee

            behavior fee : (x: Int, y: Int, c: Bool) -> Int

            let fee (x, y, c) =
                (if x == y then 10 else 20) + (if c then 1 else 2)

            example fee
            """;

    /** Two rows that both fail {@code x == y}, which no class tells from one another. */
    private static final List<String> ROWS = List.of(
            "    | (1, 2, true) -> 21\n",
            "    | (3, 4, true) -> 21\n");

    /**
     * The meeting is read, is not placed, and the behavior is short of a measurement that says
     * which: no wider run places it.
     */
    @Test
    void aMeetingTheClassesDoNotPlaceIsSaidAndLeavesTheBehaviorPartial() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MODEL + ROWS.getFirst());

        assertInstanceOf(CombinationCriterion.Interactions.class,
                behavior.evidence().combinations(),
                "the body's decisions meet, whatever this run could place of them");
        assertFalse(behavior.evidence().interaction().asked().notPlaced().isEmpty(),
                "the meeting is one the classes do not place");
        assertEquals(MeasurementStatus.PARTIAL, behavior.status(),
                () -> "so the behavior is short of a measurement: " + behavior.weakenedBy());
        assertTrue(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotPlaced.class::isInstance),
                () -> "and what it went without says which: " + behavior.weakenedBy());
    }

    /**
     * A row is credited with the combination it was seen making, and the other combinations are
     * owed.
     *
     * <p>A run is credited by what it did at the arm, so two rows the classes cannot tell apart make
     * one combination. That the classes do not state the relation only means a search for a row is
     * not steered by them.
     */
    @Test
    void aRowIsCreditedWithTheCombinationItMadeAndTheOthersAreOwed() {
        for (String rows : List.of(ROWS.getFirst(), ROWS.getFirst() + ROWS.getLast())) {
            AdequacyReport.BehaviorReport behavior = behaviorOf(MODEL + rows);
            InteractionEvidence meetings = behavior.evidence().interaction();
            assertEquals(1, meetings.made().made().orElseThrow().met().size(),
                    () -> "the else arm with c true is made by " + rows);
            assertEquals(meetings.counted() - 1, meetings.notMadeByRows().size(),
                    () -> "and every other combination is owed under " + rows);
        }
    }

    /**
     * The else of a conjunction is placed. A run is seen at the arm whichever of the two ways it
     * came, and the classes state both: it is a union of two cells and no combination is left
     * undetermined.
     */
    @Test
    void theElseOfAConjunctionIsPlacedAsTheWaysItCameBy() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module example.both

                behavior fee : (a: Bool, b: Bool, c: Bool) -> Int

                let fee (a, b, c) =
                    (if a && b then 10 else 20) + (if c then 1 else 2)

                example fee
                    | (false, false, true) -> 21
                """);

        assertTrue(behavior.evidence().interaction().asked().notPlaced().isEmpty(),
                "both ways into the else arm are classes of the input, so the meeting is placed");
        assertEquals(MeasurementStatus.COMPLETE, behavior.status(),
                () -> "and nothing is left unmeasured: " + behavior.weakenedBy());
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        List<AdequacyReport.BehaviorReport> behaviors =
                AdequacyReport.of(compilation).modules().getFirst().behaviors();
        assertEquals(1, behaviors.size(), "one behavior in the model");
        return behaviors.getFirst();
    }
}
