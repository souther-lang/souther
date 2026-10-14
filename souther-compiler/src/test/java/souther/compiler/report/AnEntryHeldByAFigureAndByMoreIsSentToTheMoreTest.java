package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Figure;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.WorkFigure;
import souther.compiler.query.EstablishmentGap;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * An entry a figure alone holds open is sent to the figure; one a figure and something else hold
 * is sent to the something else, and still names the figure.
 *
 * <p>Raising the figure lifts the first and leaves the second standing, so a reader of the second
 * told only the figure would raise it and find the entry where it was.
 */
class AnEntryHeldByAFigureAndByMoreIsSentToTheMoreTest {

    private static final Figure DEPTH = WorkFigure.OBSERVED_DEPTH.at(3);

    private static final Subject BEHAVIOR = new Subject.OfABehavior("b");

    private static final Incompleteness.Cause CUT_SHORT =
            Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED, DEPTH);

    private static final Incompleteness.Cause UNREADABLE =
            Incompleteness.Cause.of(Incompleteness.Code.VALUE_UNREADABLE);

    @Test
    void anEntryAFigureAloneHoldsIsSentToTheFigure() {
        ReaderDisposition.StoppedAtAFigure sent = assertInstanceOf(
                ReaderDisposition.StoppedAtAFigure.class,
                ReaderDisposition.of(new AdequacyUncertainty.ShowingStopped(BEHAVIOR,
                        EstablishmentGap.Observation.of(List.of(CUT_SHORT)), List.of())));

        assertEquals(List.of(DEPTH), sent.figures());
    }

    @Test
    void anEntryAFigureAndSomethingElseHoldIsSentToTheSomethingElseAndNamesTheFigure() {
        AdequacyUncertainty both = new AdequacyUncertainty.ShowingStopped(BEHAVIOR,
                EstablishmentGap.Observation.of(List.of(CUT_SHORT, UNREADABLE)), List.of());

        assertInstanceOf(ReaderDisposition.LookAtWhatShowedNoRow.class,
                ReaderDisposition.of(both));
        assertEquals(List.of(DEPTH), both.figures(), "the figure it reached is still its own");
    }

    /**
     * Two showings of one behavior stopped alike but for the figures are one entry, met at both:
     * the codes are what it is, and the figures what each met.
     */
    @Test
    void twoShowingsStoppedAlikeButForTheFiguresAreOneEntryAtBoth() {
        Figure text = WorkFigure.OBSERVED_TEXT.at(5);
        AdequacyUncertainty.ShowingStopped one = new AdequacyUncertainty.ShowingStopped(BEHAVIOR,
                EstablishmentGap.Observation.of(List.of(CUT_SHORT)), List.of());
        AdequacyUncertainty.ShowingStopped other = new AdequacyUncertainty.ShowingStopped(BEHAVIOR,
                EstablishmentGap.Observation.of(List.of(
                        Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED, text))),
                List.of());

        assertEquals(one.fact(), other.fact());
        assertEquals(List.of(DEPTH, text), one.together(other).figures());
    }
}
