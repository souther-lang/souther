package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.WrittenOutElements;
import souther.compiler.numeric.UnheldNumber;
import souther.compiler.observe.Figure;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RunSensitivity;
import souther.compiler.observe.WorkFigure;
import souther.compiler.query.EstablishmentGap;
import souther.compiler.query.ReadingReasons;
import souther.exact.ExactFailures;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A gap a wider run may close says which figure to widen, and a gap no wider run closes says none.
 *
 * <p>The report tells a reader that a figure of this compiler's stopped something wherever a gap
 * answers {@link RunSensitivity#MAY_CHANGE}. Without the figure that sentence names nothing, and a
 * figure beside a gap a wider run meets again sends the reader to widen something that changes
 * nothing. So the two answers are held to each other over every arm, and the figures to the ones
 * that were met.
 */
class AGapNamesAFigureExactlyWhereAWiderRunMayCloseItTest {

    private static final Figure DEPTH = WorkFigure.OBSERVED_DEPTH.at(3);

    private static final Figure TEXT = WorkFigure.OBSERVED_TEXT.at(5);

    /** Every reading gap there is: one of each arm, and of each code a value arrives unread with. */
    @Test
    void aReadingGapNamesAFigureExactlyWhereAWiderRunMayChangeIt() {
        for (ReadingGap each : everyReadingGap()) {
            assertEquals(each.runSensitivity() == RunSensitivity.MAY_CHANGE,
                    !each.figures().isEmpty(),
                    () -> each + " answers " + each.runSensitivity() + " and names "
                            + each.figures());
        }
    }

    /** And the figure each names is the one it was declined or stopped at. */
    @Test
    void aReadingGapNamesTheFigureItWasStoppedAt() {
        assertEquals(List.of(CompositionBudget.READINGS_OF_ONE_CONDITION.figure()),
                new ReadingGap.ReachNotRead(ReadingGap.ReachNotRead.Why.MORE_READINGS_THAN_ARE_MADE)
                        .figures());
        assertEquals(List.of(WorkFigure.ELEMENTS_A_WALK_WRITES_OUT.at(
                        WrittenOutElements.MOST_WALKED)),
                new ReadingGap.ReachNotRead(
                        ReadingGap.ReachNotRead.Why.MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT).figures());
        assertEquals(List.of(DEPTH), ReadingGap.ofAComparisonOf(new ObservedValue.Sequence(
                        List.of(new ObservedValue.Truncated(DEPTH)))).figures(),
                "a value the walk stopped says the figure the walk stopped it at");
    }

    /** An observation a figure decides is not made without the figure, and one no figure decides
     *  is not made with one. */
    @Test
    void anObservationIsNotMadeWithoutTheFigureThatDecidedIt() {
        assertThrows(IllegalArgumentException.class,
                () -> new ReadingGap.Observation(Incompleteness.Code.VALUE_TRUNCATED, List.of()));
        assertThrows(IllegalArgumentException.class,
                () -> new ReadingGap.Observation(Incompleteness.Code.VALUE_UNREADABLE,
                        List.of(DEPTH)));
    }

    /**
     * One code met at two figures is one reason, met at both.
     *
     * <p>What a reader is told once is the code, so two readings of one point stopped by two
     * limits are one sentence; and what would widen it is either limit, so neither is dropped.
     */
    @Test
    void oneCodeAtTwoFiguresIsOneReasonAtBoth() {
        ReadingReasons met = ReadingReasons.of(List.of(
                        ReadingGap.of(Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED,
                                TEXT)),
                        ReadingGap.NO_VALUE,
                        ReadingGap.of(Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED,
                                DEPTH))),
                StandingAtAPoint.ReadingsTried.EVERY_ONE);

        assertEquals(List.of(new ReadingGap.Observation(Incompleteness.Code.VALUE_TRUNCATED,
                        List.of(DEPTH, TEXT)), ReadingGap.NO_VALUE),
                met.eachKindOnce().written());
    }

    /** Every establishment gap, over each way its parts meet. */
    @Test
    void anEstablishmentGapNamesAFigureExactlyWhereAWiderRunMayCloseIt() {
        Incompleteness.Cause aLimit =
                Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED, DEPTH);
        Incompleteness.Cause nothingReadIt =
                Incompleteness.Cause.of(Incompleteness.Code.VALUE_UNREADABLE);
        Set<CompositionBudget> budgets = Set.of(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT,
                CompositionBudget.STEPS_A_SEARCH_MAY_TAKE);
        Set<CompositionRepertoire> writesSomeOf =
                Set.of(CompositionRepertoire.PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE);
        Set<CompositionCapacity> noRoom = Set.of(new CompositionCapacity(
                CompositionCapacity.Where.PLACES_A_PAIR_IS_WALKED_TO,
                UnheldNumber.of(ExactFailures.room())));

        Map<EstablishmentGap, List<Figure>> named = Map.of(
                EstablishmentGap.Observation.of(List.of(aLimit)), List.of(DEPTH),
                EstablishmentGap.Observation.of(List.of(nothingReadIt)), List.of(),
                EstablishmentGap.Observation.of(List.of(aLimit, nothingReadIt)), List.of(),
                EstablishmentGap.Composition.of(budgets),
                        Figure.inOrder(budgets.stream().map(CompositionBudget::figure).toList()),
                EstablishmentGap.Composition.of(budgets, writesSomeOf, Set.of()), List.of(),
                EstablishmentGap.Composition.of(budgets, Set.of(), noRoom), List.of(),
                EstablishmentGap.Composition.of(Set.of(), writesSomeOf, Set.of()), List.of());

        for (Map.Entry<EstablishmentGap, List<Figure>> each : named.entrySet()) {
            EstablishmentGap gap = each.getKey();
            assertEquals(gap.runSensitivity() == RunSensitivity.MAY_CHANGE,
                    !gap.figures().isEmpty(),
                    () -> gap + " answers " + gap.runSensitivity() + " and names "
                            + gap.figures());
            assertEquals(Set.copyOf(each.getValue()), Set.copyOf(gap.figures()),
                    () -> "the figures " + gap + " names");
        }
    }

    /** An observation holding a code a figure decides is not made without one. */
    @Test
    void anObservationOfTheEstablishingIsNotMadeWithoutTheFigure() {
        assertThrows(IllegalArgumentException.class, () -> EstablishmentGap.Observation.of(
                Set.of(Incompleteness.Code.VALUE_TRUNCATED), List.of()));
        assertThrows(IllegalArgumentException.class, () -> EstablishmentGap.Observation.of(
                Set.of(Incompleteness.Code.VALUE_UNREADABLE), List.of(DEPTH)));
    }

    private static List<ReadingGap> everyReadingGap() {
        List<ReadingGap> out = new ArrayList<>();
        for (Class<?> permitted : ReadingGap.class.getPermittedSubclasses()) {
            switch (permitted.getSimpleName()) {
                case "Observation" -> {
                    out.add(ReadingGap.of(new ObservedValue.Truncated(TEXT).cause()));
                    out.add(ReadingGap.of(new ObservedValue.Unknown("nothing read it").cause()));
                    out.add(ReadingGap.of(Limits.DEFAULT.stoppedBy(
                            new ObservedValue.Text("x".repeat(Limits.DEFAULT.maxText() + 1)))));
                }
                case "NoValue" -> out.add(ReadingGap.NO_VALUE);
                case "CouldNotWalk" -> out.add(ReadingGap.COULD_NOT_WALK);
                case "CouldNotReadRow" -> out.add(ReadingGap.COULD_NOT_READ_ROW);
                case "CouldNotWorkOut" -> {
                    for (UnheldNumber why : UnheldNumber.values()) {
                        out.add(ReadingGap.of(why));
                    }
                }
                case "ReachNotRead" -> {
                    for (ReadingGap.ReachNotRead.Why why : ReadingGap.ReachNotRead.Why.values()) {
                        out.add(new ReadingGap.ReachNotRead(why));
                    }
                }
                default -> fail("a reading gap this cannot make: " + permitted);
            }
        }
        return out;
    }
}
