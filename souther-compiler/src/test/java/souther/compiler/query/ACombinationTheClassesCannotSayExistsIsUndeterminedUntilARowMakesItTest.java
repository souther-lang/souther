package souther.compiler.query;

import souther.compiler.ACompiledModel;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination of a meeting whose decisions the classes of the input do not state is asked for, and
 * the classes cannot say it exists. The measure is made in full over it, and what is open is the
 * obligation: whether a row can be written, which a row a search composed and a run was seen making
 * it with answers.
 *
 * <p>The first operand below is a relation between two positions, which no class of either states.
 * So its outcomes narrow no position, and no cell steers a row into one of the meeting's
 * combinations rather than another. A row is credited with a combination by what its run did.
 */
class ACombinationTheClassesCannotSayExistsIsUndeterminedUntilARowMakesItTest {

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
     * The meeting is read and walked in full, so the measure went without nothing; and every
     * combination the rows did not make is owed a finding, which says what is open about it
     * until a run is seen making it.
     */
    @Test
    void theCombinationsNothingMadeAreOwedAndTheMeasureIsWhole() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MODEL + ROWS.getFirst());
        InteractionEvidence meetings = behavior.evidence().interaction();

        assertInstanceOf(CombinationCriterion.Interactions.class,
                behavior.evidence().combinations(),
                "the body's decisions meet, whatever this run could place of them");
        assertEquals(MeasurementStatus.COMPLETE, behavior.status(),
                () -> "the measure is made in full: " + behavior.weakenedBy());
        assertEquals(meetings.counted() - 1, meetings.notMadeByRows().size(),
                "and every combination but the one the row made is owed");
        assertTrue(meetings.notStatedToExist().size() > 0,
                "the relation is one no class states, so the classes do not say they exist");
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

    /** With a row at every combination there is nothing the classes leave open. */
    @Test
    void aRowAtEveryCombinationLeavesNothingOwed() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MODEL
                + "    | (1, 1, true) -> 11\n"
                + "    | (1, 1, false) -> 12\n"
                + "    | (1, 2, true) -> 21\n"
                + "    | (1, 2, false) -> 22\n");

        assertEquals(MeasurementStatus.COMPLETE, behavior.status(),
                () -> "every combination was made: " + behavior.weakenedBy());
        assertTrue(behavior.evidence().interaction().notMadeByRows().isEmpty(),
                "and none is owed");
    }

    /**
     * The else of a conjunction is placed. A run is seen at the arm whichever of the two ways it
     * came, and the classes state both: it is a union of two cells and every combination is
     * stated.
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

        assertTrue(behavior.evidence().interaction().asked().unconfirmed().isEmpty(),
                "both ways into the else arm are classes of the input, so every combination is"
                        + " stated");
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
