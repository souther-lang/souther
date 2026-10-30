package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementsWrittenOut;
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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A gap names every figure it reached, and a gap a wider run may close always names one.
 *
 * <p>Two questions, held apart. Which figures were reached is what happened; whether a run allowed
 * more of them closes the gap is asked of everything that stopped it. The report tells a reader a
 * figure of this compiler's stopped something wherever a gap answers
 * {@link RunSensitivity#MAY_CHANGE}, and without the figure that sentence names nothing — so that
 * direction is held over every arm. The other is not: a gap stopped at a figure and at something a
 * wider run meets again reached the figure, and a reader told it reached none would raise none and
 * meet the figure once the other thing is lifted.
 */
class AGapNamesEveryFigureItReachedTest {

    private static final Figure DEPTH = WorkFigure.OBSERVED_DEPTH.at(3);

    private static final Figure TEXT = WorkFigure.OBSERVED_TEXT.at(5);

    /** Every reading gap there is: one of each arm, and of each code a value arrives unread with. */
    @Test
    void aReadingGapAWiderRunMayChangeNamesAFigure() {
        for (ReadingGap each : everyReadingGap()) {
            if (each.runSensitivity() == RunSensitivity.MAY_CHANGE) {
                assertFalse(each.figures().isEmpty(),
                        () -> each + " answers MAY_CHANGE and names no figure");
            }
        }
    }

    /** And the figure each names is the one it was declined or stopped at. */
    @Test
    void aReadingGapNamesTheFigureItWasStoppedAt() {
        assertEquals(List.of(CompositionBudget.READINGS_OF_ONE_CONDITION.figure()),
                new ReadingGap.ReachNotRead(ReadingGap.ReachNotRead.Why.MORE_READINGS_THAN_ARE_MADE)
                        .figures());
        assertEquals(List.of(WorkFigure.ELEMENTS_A_WALK_WRITES_OUT.at(
                        ElementsWrittenOut.MOST_WALKED)),
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

    /**
     * Every establishment gap, over each way its parts meet: the figures it reached whatever else
     * stopped it, and how a wider run meets it asked of all of them.
     */
    @Test
    void anEstablishmentGapNamesEveryFigureItReachedHoweverAWiderRunMeetsIt() {
        Incompleteness.Cause aLimit =
                Incompleteness.Cause.at(Incompleteness.Code.VALUE_TRUNCATED, DEPTH);
        Incompleteness.Cause nothingReadIt =
                Incompleteness.Cause.of(Incompleteness.Code.VALUE_UNREADABLE);
        Set<CompositionBudget> budgets = Set.of(CompositionBudget.PLACES_A_PAIR_IS_TRIED_AT,
                CompositionBudget.STEPS_A_SEARCH_MAY_TAKE);
        List<Figure> budgetFigures =
                Figure.inOrder(budgets.stream().map(CompositionBudget::figure).toList());
        Set<CompositionRepertoire> writesSomeOf =
                Set.of(CompositionRepertoire.PLACES_A_PAIR_IS_TRIED_AT_ON_A_LINE);
        Set<CompositionCapacity> noRoom = Set.of(new CompositionCapacity(
                CompositionCapacity.Where.PLACES_A_PAIR_IS_WALKED_TO,
                UnheldNumber.of(ExactFailures.room())));

        Map<EstablishmentGap, Reached> named = Map.of(
                EstablishmentGap.Observation.of(List.of(aLimit)),
                new Reached(List.of(DEPTH), RunSensitivity.MAY_CHANGE),
                EstablishmentGap.Observation.of(List.of(nothingReadIt)),
                new Reached(List.of(), RunSensitivity.UNAFFECTED),
                EstablishmentGap.Observation.of(List.of(aLimit, nothingReadIt)),
                new Reached(List.of(DEPTH), RunSensitivity.UNAFFECTED),
                EstablishmentGap.Composition.of(budgets),
                new Reached(budgetFigures, RunSensitivity.MAY_CHANGE),
                EstablishmentGap.Composition.of(budgets, writesSomeOf, Set.of()),
                new Reached(budgetFigures, RunSensitivity.UNAFFECTED),
                EstablishmentGap.Composition.of(budgets, Set.of(), noRoom),
                new Reached(budgetFigures, RunSensitivity.UNAFFECTED),
                EstablishmentGap.Composition.of(Set.of(), writesSomeOf, Set.of()),
                new Reached(List.of(), RunSensitivity.UNAFFECTED));

        named.forEach((gap, reached) -> {
            assertEquals(reached.figures(), gap.figures(), () -> "the figures " + gap + " names");
            assertEquals(reached.sensitivity(), gap.runSensitivity(),
                    () -> "how a wider run meets " + gap);
        });
    }

    /** What a gap reached, and how a wider run meets it. */
    private record Reached(List<Figure> figures, RunSensitivity sensitivity) {}

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
                case "KeysNotTold" -> out.add(ReadingGap.KEYS_NOT_TOLD);
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
