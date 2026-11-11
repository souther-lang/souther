package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.values.Operand;
import souther.compiler.values.Value;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A place held to a value the source wrote is the comparison of that place with the value, about
 * the value the sameness was of: two names for two elements of one container are two values at
 * one position, and what is said of one is not said of the other.
 */
class ASamenessAgainstAWrittenValueIsAComparisonOfTheSameValueTest {

    private static final TermPath TAGS = TermPath.of("x").then("tags").element();

    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "f");
    private static final ValueIdentity A = new ValueIdentity.OfAnElement(new BindingId(OWNER, 1));
    private static final ValueIdentity B = new ValueIdentity.OfAnElement(new BindingId(OWNER, 2));

    private static Proposition.SameValue held(ValueIdentity identity, Value value,
                                              boolean holds) {
        return new Proposition.SameValue(new DecisionSubject.AnInput(TAGS, identity),
                new Operand.Written<>(value), holds);
    }

    private static DecisionAtom.OfTheInput atomOf(Proposition.Compared compared) {
        Relation.Ordered ordered = (Relation.Ordered) compared.relation();
        return (DecisionAtom.OfTheInput) ordered.term();
    }

    @Test
    void theComparisonIsAboutTheValueTheSamenessWasOf() {
        for (ValueIdentity identity : new ValueIdentity[] {
            ValueIdentity.AT_THE_POSITION, A, B }) {
            Proposition.Compared compared = held(identity, Value.text("K"), true).asAComparison();
            assertEquals(identity, atomOf(compared).identity());
            assertEquals(new NumericTerm.ValueOf(TAGS), atomOf(compared).term());
        }
    }

    @Test
    void twoNamesForTwoElementsOfOneContainerAreTwoComparisons() {
        Proposition.Compared ofA = held(A, Value.text("K"), true).asAComparison();
        Proposition.Compared ofB = held(B, Value.text("K"), true).asAComparison();
        assertNotEquals(ofA.heldSpelling(), ofB.heldSpelling());
        assertNotEquals(ofA, ofB);
    }

    @Test
    void aNumberIsTheSameWhicheverValueIdentityItIsRead() {
        for (ValueIdentity identity : new ValueIdentity[] { ValueIdentity.AT_THE_POSITION, A }) {
            Proposition.Compared compared = held(identity, Value.number(5), true).asAComparison();
            Relation.Affine affine = (Relation.Affine) compared.relation();
            assertEquals(1, affine.form().coefs().size());
            DecisionAtom.OfTheInput atom = (DecisionAtom.OfTheInput) affine.form().coefs()
                    .keySet().iterator().next();
            assertEquals(identity, atom.identity());
        }
    }

    @Test
    void aSamenessApartIsTheComparisonDenied() {
        assertEquals(true, held(A, Value.text("K"), true).asAComparison().holds());
        assertEquals(false, held(A, Value.text("K"), false).asAComparison().holds());
        assertEquals(held(A, Value.text("K"), false).asAComparison().heldSpelling(),
                held(A, Value.text("K"), true).asAComparison().heldSpelling());
    }

    @Test
    void whatIsNotAValueOnAnOrderIsNoComparison() {
        assertNull(held(A, Value.truth(true), true).asAComparison());
        assertNull(new Proposition.SameValue(new DecisionSubject.AnInput(TAGS, A),
                new DecisionSubject.AnInput(TermPath.of("x").then("other"), A), true)
                .asAComparison());
    }
}
