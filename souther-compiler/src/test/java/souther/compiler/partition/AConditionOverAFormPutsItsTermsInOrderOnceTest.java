package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * A condition over a form keeps its terms in the one order once asked for
 * ({@link TakenConstraint.TermsInOrder}), and is no other value for it: equal where its form and
 * relation are, hashed and written as a record of those two is.
 */
class AConditionOverAFormPutsItsTermsInOrderOnceTest {

    private static final NumericTerm B = new NumericTerm.ValueOf(TermPath.of("b"));
    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));

    /** Written with its terms out of the one order. */
    private static TakenConstraint.Affine bAndA() {
        return new TakenConstraint.Affine(LinearForm.sumOfAtoms(B, A), Rel.GE);
    }

    /** What a condition is, as a record of it alone. */
    private record WhatItHolds(LinearForm<NumericTerm> form, Rel rel) {}

    @Test
    void theTermsAreTheOnesPutInTheOneOrderAndArePutInOrderOnce() {
        TakenConstraint.Affine condition = bAndA();

        assertEquals(List.copyOf(NumericTerms.setInOrder(condition.form().coefs().keySet())),
                List.copyOf(condition.terms()));
        assertSame(condition.terms(), condition.terms(), "kept once asked for");
    }

    @Test
    void aConditionAskedForItsTermsIsTheValueItWasBefore() {
        TakenConstraint.Affine asked = bAndA();
        asked.terms();

        assertEquals(bAndA(), asked);
        assertEquals(bAndA().hashCode(), asked.hashCode());
        assertEquals(new WhatItHolds(asked.form(), asked.rel()).hashCode(), asked.hashCode(),
                "hashed as a record of its form and relation, so a set of them is laid out as"
                        + " it was");
    }

    @Test
    void aCellHandedInIsNotTheOneKept() {
        TakenConstraint.Affine asked = bAndA();
        TakenConstraint.Affine handed =
                new TakenConstraint.Affine(asked.form(), asked.rel(), asked.inOrder());

        assertNotSame(asked.inOrder(), handed.inOrder());
        assertEquals(asked, handed);
    }

    @Test
    void aConditionIsWrittenAsItsFormAndRelation() {
        TakenConstraint.Affine condition = bAndA();

        assertEquals(new WhatItHolds(condition.form(), condition.rel()).toString()
                .replaceFirst("^WhatItHolds", "Affine"), condition.toString());
    }
}
