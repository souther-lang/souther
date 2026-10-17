package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Evaluations;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.InjectedAnswer;
import souther.compiler.meaning.Proposition;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A value composed for an answer along a way that left a choice unchosen is not taken to meet the
 * statement the choice is of.
 *
 * <p>The figure stopped the walk before the choice's group found a way open, so the value was
 * composed against what the way chose and nothing of what the choice asks. The statement is said
 * to be one the figure stopped the looking for, which is what keeps a reader of the answer from
 * counting it met; the statement whose every choice was chosen is met.
 */
class AChoiceTheLookingNeverReachedIsNotTakenAsMetTest {

    private static final AnswerDemand.AStatement CHOSEN = statement(0);

    private static final AnswerDemand.AStatement LEFT = statement(1);

    private static final AnAnswerComposed.Asked ASKED_OF_CHOSEN =
            new AnAnswerComposed.Asked(CHOSEN, truth("p"));

    private static final AnAnswerComposed.Asked ASKED_OF_LEFT =
            new AnAnswerComposed.Asked(LEFT, new DemandReading.Read.OneOf(
                    List.of(List.of(truth("b1")), List.of(truth("b2"))), Optional.empty()));

    private static final List<AnAnswerComposed.Pending> PENDING = List.of(
            new AnAnswerComposed.Pending(CHOSEN, List.of(ASKED_OF_CHOSEN.read()), Set.of()),
            new AnAnswerComposed.Pending(LEFT, List.of(ASKED_OF_LEFT.read()), Set.of()));

    @Test
    void theStatementOfAChoiceLeftUnchosenIsSaidToBeOneTheFigureStopped() {
        List<List<AnAnswerComposed.Asked>> composedAlong = new ArrayList<>();
        AnAnswerComposed.Attempt attempt = AnAnswerComposed.composedAlongTheWays(
                new OneOfEach.Walked.Open<>(List.of(new OneOfEach.Way.LeftUnchosen<>(
                        List.of(ASKED_OF_CHOSEN), List.of(ASKED_OF_LEFT))),
                        CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT),
                way -> composed(way, composedAlong), List.of(), PENDING);

        assertEquals(List.of(List.of(ASKED_OF_CHOSEN)), composedAlong,
                "composed along what the way chose");
        assertInstanceOf(AnAnswerComposed.Outcome.Composed.class, attempt.outcome());
        assertEquals(List.of(new DemandGap.Uncomposed(LEFT,
                        DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded.by(
                                Set.of(CompositionBudget.CHOICES_ON_A_WAY_LOOKED_AT)))),
                attempt.unaccounted(),
                "the statement left unchosen is not met, and the figure is why");
    }

    /** The control: the same statements along a way that chose every choice are met. */
    @Test
    void aWayThatChoseEveryChoiceMeetsEveryStatement() {
        List<List<AnAnswerComposed.Asked>> composedAlong = new ArrayList<>();
        AnAnswerComposed.Attempt attempt = AnAnswerComposed.composedAlongTheWays(
                new OneOfEach.Walked.Open<>(List.of(new OneOfEach.Way.Chosen<>(
                        List.of(ASKED_OF_CHOSEN, new AnAnswerComposed.Asked(LEFT,
                                truth("b1"))), Map.of())), null),
                way -> composed(way, composedAlong), List.of(), PENDING);

        assertInstanceOf(AnAnswerComposed.Outcome.Composed.class, attempt.outcome());
        assertEquals(List.of(), attempt.unaccounted());
    }

    /** A value composed along {@code way}, which is recorded. */
    private static AnAnswerComposed.Attempt composed(List<AnAnswerComposed.Asked> way,
                                                    List<List<AnAnswerComposed.Asked>> into) {
        into.add(way);
        return AnAnswerComposed.Attempt.of(
                new AnAnswerComposed.Outcome.Composed(FixtureTemplate.bool(true)));
    }

    private static AnswerDemand.AStatement statement(int occurrence) {
        return new AnswerDemand.AStatement(
                new InjectedAnswer(Evaluations.of(
                        new ValueName.Behavior("example.answered", "look"), 0), List.of()),
                new ConditionReportAnchor.WhereTheReadingMetIt("m",
                        new ConditionOccurrence(
                                "b", ConditionOccurrence.Reading.DIVIDING, occurrence)),
                new Proposition.Always(true), List.of());
    }

    private static DemandReading.Read truth(String field) {
        return new DemandReading.Read.Demands(
                new RowDemand.ATruth(TermPath.of("$answer").then(field), true));
    }
}
