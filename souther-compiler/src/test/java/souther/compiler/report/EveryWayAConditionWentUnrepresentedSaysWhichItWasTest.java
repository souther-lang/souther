package souther.compiler.report;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.AnswerDemand;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.ConditionGap;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.ConditionReportAnchor;
import souther.compiler.partition.DecisionAtom;
import souther.compiler.partition.DecisionSubject;
import souther.compiler.partition.DemandGap;
import souther.compiler.partition.InjectedAnswer;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.ReachabilityGap;
import souther.compiler.partition.TakenConstraint;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every way a condition on the way went unrepresented has a sentence of its own, and they are not
 * each other's.
 *
 * <p><b>What a reader does about them differs, so the words have to.</b> A condition this reading
 * had no words for is one to write differently; one whose positions nothing could build a value at
 * is one this compiler fell short at; one naming another number of a location the row is already
 * being written for is one nobody has written the composing for. Rendered alike, an author is sent
 * to look for the rule that refuses a row nothing refuses.
 *
 * <p><b>Driven by the seals rather than by a list here.</b> A way added is a leaf of
 * {@link ReachabilityGap.Why} or of one of {@link DemandGap}'s, and a leaf with nothing written for
 * it would reach a reader as whichever sentence the arm beside it has — which is the same shape of
 * defect as a capability this compiler is short of being published as a value the model does not
 * have.
 *
 * <p><b>Both subjects, and no sentence shared between them.</b> A condition about the input and a
 * condition about what a dependency answers go unrepresented for reasons that look alike and are
 * about different things, and an author handed the input's words for an answer's shortfall would go
 * looking at positions the condition is not over.
 */
class EveryWayAConditionWentUnrepresentedSaysWhichItWasTest {

    /** What the two sentences a reader may not be handed for each other are about. */
    private static final String ABOUT_THE_POSITIONS = "positions nothing here composed a value at";
    private static final String ABOUT_ANOTHER_NUMBER = "another number taken where this row is"
            + " already being written for one";

    /** Every way there is says something, and no two of them say the same thing. */
    @Test
    void eachWaySaysSomethingOfItsOwn() {
        Map<Class<?>, ConditionGap> ways = theWays();

        assertEquals(everyWayThereIs(), List.copyOf(ways.keySet()),
                "every way a condition goes unrepresented is one this asks for a sentence");
        List<String> said = new ArrayList<>();
        for (ConditionGap gap : ways.values()) {
            String sentence = AdequacyReport.whyLeftOut(gap);
            assertNotNull(sentence, () -> "a sentence for " + gap);
            assertFalse(sentence.isBlank(), () -> "a sentence for " + gap);
            said.add(sentence);
        }

        assertEquals(said.size(), Set.copyOf(said).size(),
                () -> "and no two of the ways are told the same way: " + said);
    }

    /** The leaves of every vocabulary a gap's reason is said in, in the order the seals name
     *  them. */
    private static List<Class<?>> everyWayThereIs() {
        List<Class<?>> out = new ArrayList<>(armsOf(ReachabilityGap.Why.class));
        out.addAll(armsOf(DemandGap.WhyNotStated.class));
        out.addAll(armsOf(DemandGap.WhyNotComposed.class));
        return out;
    }

    /**
     * And the one this compiler's reach turns on is not told as the one about the positions.
     *
     * <p>Held by name rather than only by being different, because these two are the pair that says
     * whether an author has a row to write. A location asked for numbers nothing composes one value
     * for is a row this compiler cannot write yet; positions nothing composed a value at is what it
     * says of a position it could not build one for at all.
     */
    @Test
    void aLocationAskedForNumbersNothingComposesOneValueForIsNotToldAsAPositionNothingBuiltAt() {
        String numbers = AdequacyReport.whyLeftOut(ofTheInput(
                new ReachabilityGap.Why.TwoNumbersAtOneLocation()));
        String positions = AdequacyReport.whyLeftOut(ofTheInput(
                new ReachabilityGap.Why.NoValueComposedForItsPositions()));

        assertTrue(numbers.contains(ABOUT_ANOTHER_NUMBER), () -> numbers);
        assertFalse(numbers.contains(ABOUT_THE_POSITIONS), () -> numbers);
        assertTrue(positions.contains(ABOUT_THE_POSITIONS), () -> positions);
    }

    /** One of each way, in the order the seals name them. */
    private static Map<Class<?>, ConditionGap> theWays() {
        Map<Class<?>, ConditionGap> out = new LinkedHashMap<>();
        out.put(ReachabilityGap.Why.NoValueComposedForItsPositions.class,
                ofTheInput(new ReachabilityGap.Why.NoValueComposedForItsPositions()));
        out.put(ReachabilityGap.Why.TheWalkForItsPositionsWasStopped.class,
                ofTheInput(ReachabilityGap.Why.TheWalkForItsPositionsWasStopped.by(
                        Set.of(CompositionBudget.NUMBERS_OF_A_SET_TRIED))));
        out.put(ReachabilityGap.Why.TwoNumbersAtOneLocation.class,
                ofTheInput(new ReachabilityGap.Why.TwoNumbersAtOneLocation()));
        out.put(DemandGap.WhyNotStated.ATruthOfAPlaceInsideTheAnswer.class,
                notStated(new DemandGap.WhyNotStated.ATruthOfAPlaceInsideTheAnswer()));
        out.put(DemandGap.WhyNotStated.AFormOverMoreThanOneAnswer.class,
                notStated(new DemandGap.WhyNotStated.AFormOverMoreThanOneAnswer()));
        out.put(DemandGap.WhyNotStated.APlaceOnTheAnswersOwnOrder.class,
                notStated(new DemandGap.WhyNotStated.APlaceOnTheAnswersOwnOrder()));
        out.put(DemandGap.WhyNotComposed.NoOrderUnderATermOfTheAnswer.class,
                notComposed(new DemandGap.WhyNotComposed.NoOrderUnderATermOfTheAnswer(
                        new NumericTerm.ValueOf(TermPath.of("x").then("id")))));
        out.put(DemandGap.WhyNotComposed.NoValueComposedAtItsPositions.class,
                notComposed(new DemandGap.WhyNotComposed.NoValueComposedAtItsPositions()));
        out.put(DemandGap.WhyNotComposed.NothingComposedAValueOfTheAnswer.class,
                notComposed(new DemandGap.WhyNotComposed.NothingComposedAValueOfTheAnswer()));
        out.put(DemandGap.WhyNotComposed.OneValueAnswersEveryCall.class,
                notComposed(new DemandGap.WhyNotComposed.OneValueAnswersEveryCall()));
        return out;
    }

    private static ConditionGap ofTheInput(ReachabilityGap.Why why) {
        return new ConditionGap.OfTheInput(new ReachabilityGap.Uncomposed(cut(), why));
    }

    private static ConditionGap notStated(DemandGap.WhyNotStated why) {
        return new ConditionGap.OfADemand(new DemandGap.Unstated(where(), why));
    }

    private static ConditionGap notComposed(DemandGap.WhyNotComposed why) {
        return new ConditionGap.OfADemand(new DemandGap.Uncomposed(demand(), why));
    }

    /** A demand to hang a way on, which these sentences say nothing about. */
    private static AnswerDemand demand() {
        return new AnswerDemand.AComparison(
                new InjectedAnswer(new ValueName.Behavior("m", "look"), List.of()),
                where(),
                LinearForm.atom(new DecisionAtom.OfAnAnswer(new DecisionSubject.AnAnswer(
                        new InjectedAnswer(new ValueName.Behavior("m", "look"), List.of()),
                        List.of()))),
                Rel.GE);
    }

    /** A condition to hang a way on, which these sentences say nothing about. */
    private static OnTheWay.TakenIn cut() {
        return new OnTheWay.TakenIn(where(),
                new TakenConstraint.Affine(
                        LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("x"))), Rel.GE));
    }

    /** Which question a report about the condition under test would put. */
    private static ConditionReportAnchor where() {
        return new ConditionReportAnchor.WhereTheReadingMetIt("m",
                new ConditionOccurrence("f", 0));
    }

    /** The leaves of a seal, which is what its ways are. */
    private static List<Class<?>> armsOf(Class<?> seal) {
        List<Class<?>> out = new ArrayList<>();
        for (Class<?> each : seal.getPermittedSubclasses()) {
            if (each.isSealed()) {
                out.addAll(armsOf(each));
            } else {
                out.add(each);
            }
        }
        return out;
    }
}
