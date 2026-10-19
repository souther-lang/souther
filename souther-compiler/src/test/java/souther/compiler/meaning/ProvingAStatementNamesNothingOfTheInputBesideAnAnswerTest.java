package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Evaluations;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A statement is about an answer alone only where it is read to the end and names nothing of the
 * input beside it. A part nothing read is not that: what it leaves unsaid may be a position of the
 * input, so it is not proved to name none.
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

        assertTrue(Proposition.aboutAnAnswerAlone(truth));
        assertTrue(Proposition.aboutAnAnswerAlone(
                new Proposition.Some(rows(), truth, true)));
    }

    @Test
    void anElementStatementNothingReadIsNotProvedToNameNothingOfTheInput() {
        assertFalse(Proposition.aboutAnAnswerAlone(
                new Proposition.Some(rows(), nothingRead(), true)));
    }

    @Test
    void aPartNothingReadBesideAStatementOfTheAnswerIsNotProvedEither() {
        Proposition truth = new Proposition.Truth(rows().element(), true);

        assertFalse(Proposition.aboutAnAnswerAlone(
                Proposition.all(List.of(truth, nothingRead()))));
    }

    @Test
    void aSearchFromAPositionOfTheInputIsAboutTheInputWhatItAsksOfTheAnswer() {
        Proposition atANode = new Proposition.Truth(rows().element(), true);
        Proposition search = new Proposition.SomeReachable(TermPath.of("t"), TermPath.of("t"),
                List.of("children"), atANode, Optional.of(atANode), true);

        assertFalse(Proposition.aboutAnAnswerAlone(search));
    }

    @Test
    void aStatementThatNamesAPositionOfTheInputBesideTheAnswerIsNot() {
        Proposition sameKey = new Proposition.SameValue(rows().element(),
                new DecisionSubject.AnInput(TermPath.of("sku")), true);

        assertFalse(Proposition.aboutAnAnswerAlone(
                new Proposition.Some(rows(), sameKey, true)));
    }
}
