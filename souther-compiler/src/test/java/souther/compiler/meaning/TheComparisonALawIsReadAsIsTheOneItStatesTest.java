package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a law says of two things is read as a comparison of an element or a key with a value, and
 * the comparison is the law's only where it is the equality of the two, held where the law holds
 * them one and not where it holds them apart.
 *
 * <p>The reading that made the comparison bound its sides itself, so what it says of the law is
 * checked of the law: a comparison of another relation, or of the other polarity, or of a law
 * that holds two elements and no value, would be the reading of another statement taken for this
 * one.
 */
class TheComparisonALawIsReadAsIsTheOneItStatesTest {

    private static final Quantity VALUE = at(TermPath.of("email"));

    private static final Quantity ELEMENT = at(TermPath.of("emails").element());

    private static Quantity at(TermPath place) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(place),
                ValueIdentity.AT_THE_POSITION);
    }

    private static LawProposition.Same<String> sameness(LawSubject<String> one, boolean holds) {
        return new LawProposition.Same<>(one, new LawSubject.Argument<>("v"), holds);
    }

    private static Derivation.TheSameAsAWrittenComparison read(
            LawProposition.Same<String> law, Rel rel, boolean holds) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(VALUE, ExactRatio.ONE);
        coefs.put(ELEMENT, ExactRatio.ONE.negated());
        Derivation comparison = new Derivation.AComparisonRead(
                Derivation.ComparisonReading.AS_A_CUT,
                new Relation.Affine(new LinearForm<>(ExactRatio.ZERO, coefs), rel), holds,
                Derivation.AComparisonRead.Facing.NOTHING_WRITTEN);
        return new Derivation.TheSameAsAWrittenComparison(law, comparison,
                new Derivation.Stopped(new WhyUnread.AtNoPosition(
                        WhyUnread.AtNoPosition.Place.VALUE), false));
    }

    @Test
    void theEqualityOfAnElementOrAKeyWithTheValueIsTheLawsWhereItHoldsThemOne() {
        for (LawSubject<String> one : java.util.List.of(new LawSubject.ElementOf<>("c"),
                new LawSubject.KeyOf<>("c"))) {
            LawProposition.Same<String> law = sameness(one, true);
            assertTrue(read(law, Rel.EQ, true).comparesWhatTheLawSays(law), one.toString());
        }
    }

    @Test
    void theOtherPolarityIsAnotherStatement() {
        LawProposition.Same<String> apart = sameness(new LawSubject.ElementOf<>("c"), false);
        assertTrue(read(apart, Rel.EQ, false).comparesWhatTheLawSays(apart));
        assertFalse(read(apart, Rel.EQ, true).comparesWhatTheLawSays(apart));
        LawProposition.Same<String> one = sameness(new LawSubject.ElementOf<>("c"), true);
        assertFalse(read(one, Rel.EQ, false).comparesWhatTheLawSays(one));
    }

    @Test
    void anotherRelationIsAnotherStatement() {
        LawProposition.Same<String> law = sameness(new LawSubject.ElementOf<>("c"), true);
        assertFalse(read(law, Rel.GT, true).comparesWhatTheLawSays(law));
    }

    @Test
    void aLawOfSomethingOtherThanAnElementOrAKeyAndAValueIsNotRead() {
        LawProposition.Same<String> twoElements = new LawProposition.Same<>(
                new LawSubject.ElementOf<>("c"), new LawSubject.ElementOf<>("d"), true);
        assertFalse(read(sameness(new LawSubject.ElementOf<>("c"), true), Rel.EQ, true)
                .comparesWhatTheLawSays(twoElements));
    }

    @Test
    void aComparisonNoReadingTookToTheEndSaysNothingAndIsNotRefused() {
        LawProposition.Same<String> law = sameness(new LawSubject.ElementOf<>("c"), true);
        Derivation stopped = new Derivation.Stopped(new WhyUnread.AtNoPosition(
                WhyUnread.AtNoPosition.Place.VALUE), false);
        assertTrue(new Derivation.TheSameAsAWrittenComparison(law, stopped, stopped)
                .comparesWhatTheLawSays(law));
    }
}
