package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A choice between things a value of an answer is asked keeps the alternatives it can compose
 * along, and says which figure left the others.
 *
 * <p>Any one way is enough for what is asked to hold, so an alternative a figure stopped, or one no
 * value is written toward, is passed over and the rest are taken. Only where nothing is left is the
 * choice what stopped them — and then a figure that stopped some of them is what it says, since a
 * way past the figure may be one a value meets.
 */
class AChoiceOfWaysAnAnswerMeetsKeepsWhatWasLookedAtTest {

    private static final DemandReading.Read STOPPED =
            new DemandReading.Read.Unread(new WhyNotTaken.MoreWaysThanAreRead());

    private static final DemandReading.Read NO_WORDS = new DemandReading.Read.Unread(
            new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));

    private static final DemandReading.Read NO_OTHER_WORDS = new DemandReading.Read.Unread(
            new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.AN_ANSWER_A_ROW_STANDS_IN));

    @Test
    void anAlternativeAFigureStoppedLeavesTheOtherInEitherOrder() {
        DemandReading.Read written = atLeast(3);
        for (List<List<DemandReading.Read>> alternatives : List.of(
                List.of(List.of(STOPPED), List.of(written)),
                List.of(List.of(written), List.of(STOPPED)))) {
            assertEquals(new AnAnswerComposed.Ways.Written(
                            Set.of(CompositionBudget.READINGS_OF_ONE_CONDITION)),
                    AnAnswerComposed.written(List.of(new DemandReading.Read.OneOf(alternatives,
                            Optional.empty()))),
                    "the other alternative, and the figure that left the first");
        }
    }

    @Test
    void anAlternativeNoValueIsWrittenTowardLeavesTheOther() {
        DemandReading.Read written = atLeast(3);
        assertEquals(new AnAnswerComposed.Ways.Written(Set.of()),
                AnAnswerComposed.written(List.of(new DemandReading.Read.OneOf(
                        List.of(List.of(NO_WORDS), List.of(written)), Optional.empty()))),
                "the other alternative, and no figure: nothing more looking would read");
    }

    @Test
    void whereNothingIsLeftAFigureThatStoppedSomeIsWhatTheChoiceSays() {
        assertEquals(new AnAnswerComposed.Ways.Stopped(
                        Set.of(CompositionBudget.READINGS_OF_ONE_CONDITION)),
                AnAnswerComposed.written(List.of(new DemandReading.Read.OneOf(
                        List.of(List.of(NO_WORDS), List.of(STOPPED)), Optional.empty()))));
        assertEquals(new AnAnswerComposed.Ways.Unwritable(),
                AnAnswerComposed.written(List.of(new DemandReading.Read.OneOf(
                        List.of(List.of(NO_WORDS), List.of(NO_OTHER_WORDS)), Optional.empty()))));
    }

    /**
     * A part the reading gave up at a figure is stopped at that figure, whichever it is: each says
     * the one somebody would raise, and none is a part no value is written toward.
     */
    @Test
    void aPartGivenUpAtAFigureIsStoppedAtThatFigure() {
        Map<WhyUnread, CompositionBudget> figures = Map.of(
                new WhyUnread.MoreReadingsThanAreMade(),
                CompositionBudget.READINGS_OF_ONE_CONDITION,
                new WhyUnread.MoreTotalReadingsThanAreMade(),
                CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION,
                new WhyUnread.MorePartsThanAreConcluded(),
                CompositionBudget.PARTS_A_DERIVATION_CONCLUDES);
        figures.forEach((why, figure) -> assertEquals(
                new AnAnswerComposed.Ways.Stopped(Set.of(figure)),
                AnAnswerComposed.written(List.of(
                        new DemandReading.Read.Unread(new WhyNotTaken.MeaningUnread(why)))),
                why::toString));
    }

    /** That the number at {@code $answer.n} is at least {@code level}. */
    private static DemandReading.Read atLeast(int level) {
        return new DemandReading.Read.Demands(new RowDemand.Relational(new TakenConstraint.Affine(
                LinearForm.<NumericTerm>atomMinusConstant(
                        new NumericTerm.ValueOf(TermPath.of("$answer").then("n")),
                        ExactRatio.of(level)),
                Rel.GE)));
    }
}
