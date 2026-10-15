package souther.compiler.query;

import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A meeting whose combinations the classes of the input do not place is measured by nothing, and the
 * behavior says so.
 *
 * <p>The first operand below fails into its {@code else} arm two ways — at {@code a}, and at
 * {@code b} after {@code a} held — and a run is seen at the arm either way: nothing it does tells
 * the two apart. So the arm is one way of settling that factor, and it narrows no position; no cell
 * steers a row into one of the meeting's combinations rather than another, and none is asked for.
 * Credited by what a run is seen doing, a row through the arm would have been counted as making a
 * combination it did not make; dropped without a word, the combinations would read as nothing
 * owed.
 */
class AMeetingTheClassesDoNotPlaceLeavesTheBehaviorPartialTest {

    private static final String MODEL = """
            module example.fee

            behavior fee : (a: Bool, b: Bool, c: Bool) -> Int

            let fee (a, b, c) =
                (if a && b then 10 else 20) + (if c then 1 else 2)

            example fee
            """;

    /** A row that stopped at {@code a}, and one that went on to fail {@code b}. */
    private static final List<String> ROWS = List.of(
            "    | (false, false, true) -> 21\n",
            "    | (true, false, true) -> 21\n");

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
     * No row is credited with a combination of it, whichever way into the arm the row came, and
     * nothing is owed at one either.
     */
    @Test
    void noRowIsCreditedWithACombinationAndNoneIsOwed() {
        for (String rows : List.of(ROWS.getFirst(), ROWS.getFirst() + ROWS.getLast())) {
            AdequacyReport.BehaviorReport behavior = behaviorOf(MODEL + rows);
            InteractionEvidence meetings = behavior.evidence().interaction();
            assertEquals(Set.of(), meetings.made().made().orElseThrow().met(),
                    () -> "no combination is made by " + rows);
            assertEquals(List.of(), meetings.notMadeByRows(),
                    () -> "and none is owed under " + rows);
        }
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(),
                () -> AdequacyReport.of(compilation)
                        .human(SourceRendering.namedByIdentity(compilation.texts())));
        List<AdequacyReport.BehaviorReport> behaviors =
                AdequacyReport.of(compilation).modules().getFirst().behaviors();
        assertEquals(1, behaviors.size(), "one behavior in the model");
        return behaviors.getFirst();
    }
}
