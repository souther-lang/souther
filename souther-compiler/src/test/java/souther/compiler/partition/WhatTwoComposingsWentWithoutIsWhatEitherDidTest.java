package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Evaluations;
import souther.compiler.meaning.InjectedAnswer;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.sites.WrittenCondition;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What two composings of one way went without, between them, is what either went without.
 *
 * <p>An answer made of several composings is weaker for every condition any of them could not
 * compose against. One composing's account in place of the rest leaves out what the others went
 * without, and which one stood for the rest would follow the order they were made in.
 */
class WhatTwoComposingsWentWithoutIsWhatEitherDidTest {

    /** A condition either could not compose against is kept, once. */
    @Test
    void whatEitherCouldNotComposeAgainstIsKept() {
        CompositionAccount one = CompositionAccount.ofTheInput(List.of(gap(0)));
        CompositionAccount other = CompositionAccount.ofTheInput(List.of(gap(1), gap(0)));

        assertEquals(List.of(gap(0), gap(1)), one.alongside(other).onTheWay(),
                "both conditions were gone without, and the one both went without is one");
        assertEquals(Set.copyOf(one.alongside(other).onTheWay()),
                Set.copyOf(other.alongside(one).onTheWay()),
                "whichever composing was made first");
    }

    /**
     * A condition is taken up by an answer only where both took it up.
     *
     * <p>Where one of them did not, that composing went without it — and reconciled against the
     * way it is a gap. Taken up because the other took it up, the answer would be said to have
     * gone without less than one of its composings did.
     */
    @Test
    void aConditionIsTakenUpOnlyWhereBothTookItUp() {
        ConditionOccurrence both = condition(0);
        ConditionOccurrence onlyOne = condition(1);
        CompositionAccount one = new CompositionAccount(List.of(), List.of(),
                Set.of(both, onlyOne));
        CompositionAccount other = new CompositionAccount(List.of(), List.of(), Set.of(both));

        assertEquals(Set.of(both), one.alongside(other).takenUpByAnAnswer(),
                "the other composing went without what only the first took up");
        assertEquals(one.alongside(other).takenUpByAnAnswer(),
                other.alongside(one).takenUpByAnAnswer(),
                "whichever composing was made first");
    }

    /**
     * And put in the order the reading states the conditions, the account is one value whichever
     * composing was put first.
     */
    @Test
    void inTheOrderTheConditionsAreStatedTheOrderOfPuttingTogetherIsGone() {
        CompositionAccount one = CompositionAccount.ofTheInput(List.of(gap(1)));
        CompositionAccount other = CompositionAccount.ofTheInput(List.of(gap(0)));
        WayToTheBorder way = new WayToTheBorder(List.of(declined(0), declined(1)));

        assertEquals(List.of(gap(0), gap(1)),
                one.alongside(other).inTheOrderOf(way, AnswersDemanded.NOTHING).onTheWay(),
                "the condition stated first is said first");
        assertEquals(one.alongside(other).inTheOrderOf(way, AnswersDemanded.NOTHING),
                other.alongside(one).inTheOrderOf(way, AnswersDemanded.NOTHING),
                "whichever composing was put first");
    }

    /**
     * Two calls of a helper are two conditions sent to one place, and they are said in the order
     * the way states them rather than the order the composings were put together in.
     */
    @Test
    void twoCallsOfAHelperAreSaidInTheOrderTheWayStatesThem() {
        ConditionReportAnchor written = new ConditionReportAnchor.WhereItIsWritten(
                new WrittenCondition.Construct(new SourceConstructOrigin(
                        new WrittenOwner.Body("example.helper", "either"), 0, 0,
                        SourceConstruct.BINARY)));
        OnTheWay.Declined first = declined(0, written);
        OnTheWay.Declined second = declined(1, written);
        CompositionAccount one = CompositionAccount.ofTheInput(
                List.of(new ReachabilityGap.Unstated(second)));
        CompositionAccount other = CompositionAccount.ofTheInput(
                List.of(new ReachabilityGap.Unstated(first)));
        WayToTheBorder way = new WayToTheBorder(List.of(first, second));

        assertEquals(List.of(new ReachabilityGap.Unstated(first),
                        new ReachabilityGap.Unstated(second)),
                one.alongside(other).inTheOrderOf(way, AnswersDemanded.NOTHING).onTheWay(),
                "the call the way states first is said first, though both are said at one place");
    }

    /**
     * Two conditions inside the alternatives of a condition of several ways are said in the order
     * the alternatives are kept, whichever composing was put first.
     *
     * <p>They are not on the way's top, so a placing that read the top alone put both nowhere and
     * left them in the order they were put together in.
     */
    @Test
    void conditionsInsideAlternativesAreSaidInTheOrderTheAlternativesAreKept() {
        OnTheWay.Declined inFirst = declined(1);
        OnTheWay.Declined inSecond = declined(2);
        WayToTheBorder way = new WayToTheBorder(List.of(new OnTheWay.OneOf(condition(0),
                anchor(0), List.of(List.of(inFirst), List.of(inSecond)), Optional.empty())));
        CompositionAccount one = CompositionAccount.ofTheInput(
                List.of(new ReachabilityGap.Unstated(inSecond)));
        CompositionAccount other = CompositionAccount.ofTheInput(
                List.of(new ReachabilityGap.Unstated(inFirst)));

        assertEquals(List.of(new ReachabilityGap.Unstated(inFirst),
                        new ReachabilityGap.Unstated(inSecond)),
                one.alongside(other).inTheOrderOf(way, AnswersDemanded.NOTHING).onTheWay(),
                "the first alternative's condition first");
        assertEquals(one.alongside(other).inTheOrderOf(way, AnswersDemanded.NOTHING),
                other.alongside(one).inTheOrderOf(way, AnswersDemanded.NOTHING),
                "whichever composing was put first");
    }

    /**
     * Two composings that went without one demand for two reasons say them in the order their
     * shapes are declared, and two figures in the order the figures are, whichever was put first.
     */
    @Test
    void twoReasonsAboutOneDemandAreSaidInOneOrder() {
        AnswerDemand demand = new AnswerDemand.ATruth(new InjectedAnswer(Evaluations.of(
                        new ValueName.Behavior("example.answered", "look"), 0), List.of()),
                anchor(0), List.of(), true);
        DemandGap nothingComposed = new DemandGap.Uncomposed(demand,
                new DemandGap.WhyNotComposed.NoValueComposedAtItsPositions());
        DemandGap oneValue = new DemandGap.Uncomposed(demand,
                new DemandGap.WhyNotComposed.OneValueAnswersEveryCall());
        DemandGap elements = new DemandGap.Uncomposed(demand,
                DemandGap.WhyNotComposed.NoPairComposedBeforeAFigureEnded.by(
                        Set.of(CompositionBudget.ELEMENTS_A_PROPOSAL_HOLDS)));
        DemandGap characters = new DemandGap.Uncomposed(demand,
                DemandGap.WhyNotComposed.NoPairComposedBeforeAFigureEnded.by(
                        Set.of(CompositionBudget.CHARACTERS_A_PROPOSAL_HOLDS)));
        AnswersDemanded demands = new AnswersDemanded(List.of(demand), List.of(), Set.of());

        for (List<DemandGap> met : List.of(List.of(characters, oneValue, elements, nothingComposed),
                List.of(nothingComposed, elements, oneValue, characters))) {
            CompositionAccount together = CompositionAccount.NOTHING;
            for (DemandGap each : met) {
                together = together.alongside(
                        new CompositionAccount(List.of(), List.of(each), Set.of()));
            }
            assertEquals(List.of(nothingComposed, oneValue, elements, characters),
                    together.inTheOrderOf(new WayToTheBorder(List.of()), demands).onAnAnswer(),
                    () -> "whichever was put together first: " + met);
        }
    }

    private static ReachabilityGap gap(int which) {
        return new ReachabilityGap.Unstated(declined(which));
    }

    private static OnTheWay.Declined declined(int which) {
        return declined(which, anchor(which));
    }

    private static OnTheWay.Declined declined(int which, ConditionReportAnchor anchor) {
        return new OnTheWay.Declined(condition(which), anchor,
                new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));
    }

    private static ConditionReportAnchor anchor(int which) {
        return new ConditionReportAnchor.WhereTheReadingMetIt("example.ruled", condition(which));
    }

    private static ConditionOccurrence condition(int which) {
        return new ConditionOccurrence("f", ConditionOccurrence.Reading.DECIDING, which);
    }
}
