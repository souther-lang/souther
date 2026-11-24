package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Evaluations;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a statement about an answer names of the input beside it is said only where the statement
 * is read to the end. A part nothing read is not that: what it leaves unsaid may be a position of
 * the input, so nothing is said of what it names. A statement read to the end names the positions
 * it names, and none where it asks the answer alone.
 */
class ProvingAStatementNamesNothingOfTheInputBesideAnAnswerTest {

    private static final InjectedAnswer ANSWER = new InjectedAnswer(
            Evaluations.of(new ValueName.Behavior("example", "look"), 0), List.of());

    private static DecisionSubject.AnAnswer rows() {
        return new DecisionSubject.AnAnswer(ANSWER, List.of(new TermPath.Step.Field("rows")));
    }

    private static Proposition nothingRead() {
        return new Proposition.Unread(Optional.empty(), 0, new WhyUnread.NoNumberOnARun(), false,
                true);
    }

    @Test
    void whatIsAskedOfTheAnswerAloneNamesNothingOfTheInput() {
        Proposition truth = new Proposition.Truth(rows().element(), true);

        assertEquals(Optional.of(List.of()), PositionsAStatementReads.besideAnAnswer(truth));
        assertEquals(Optional.of(List.of()), PositionsAStatementReads.besideAnAnswer(
                new Proposition.Some(rows(), truth, true)));
    }

    @Test
    void anElementStatementNothingReadIsNotProvedToNameNothingOfTheInput() {
        assertEquals(Optional.empty(), PositionsAStatementReads.besideAnAnswer(
                new Proposition.Some(rows(), nothingRead(), true)));
    }

    @Test
    void aPartNothingReadBesideAStatementOfTheAnswerIsNotProvedEither() {
        Proposition truth = new Proposition.Truth(rows().element(), true);

        assertEquals(Optional.empty(), PositionsAStatementReads.besideAnAnswer(
                Proposition.all(List.of(truth, nothingRead()))));
    }

    @Test
    void aSearchFromAPositionOfTheInputIsAboutTheInputWhatItAsksOfTheAnswer() {
        Proposition atANode = new Proposition.Truth(rows().element(), true);
        Proposition search = new Proposition.SomeReachable(TermPath.of("t"), TermPath.of("t"),
                List.of("children"), atANode, Optional.of(atANode), true);

        assertEquals(Optional.empty(), PositionsAStatementReads.besideAnAnswer(search));
    }

    @Test
    void aStatementThatNamesAPositionOfTheInputBesideTheAnswerNamesThatPosition() {
        Proposition sameKey = new Proposition.SameValue(rows().element(),
                new DecisionSubject.AnInput(TermPath.of("sku")), true);

        assertEquals(Optional.of(List.of(TermPath.of("sku"))),
                PositionsAStatementReads.besideAnAnswer(new Proposition.Some(rows(), sameKey,
                        true)));
    }

    @Test
    void aStatementAboutNoAnswerSaysNothingOfWhatItNamesBesideOne() {
        assertEquals(Optional.empty(), PositionsAStatementReads.besideAnAnswer(
                new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("flag")), true)));
    }
}
