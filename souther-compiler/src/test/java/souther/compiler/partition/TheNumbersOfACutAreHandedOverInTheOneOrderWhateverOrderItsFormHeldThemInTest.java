package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A search that places a cut's numbers one at a time takes them in the order the cut hands them
 * over, and which of several rows it comes to first is that order's answer.
 *
 * <p>A form is a mapping, so the order it holds its terms in is the order it was filled in — the
 * hash order of what the terms are made of, or a different one in each run. Two equal cuts have to
 * hand a search one sequence, and the one they hand is the one {@link NumericTerms} walks a form
 * in.
 */
class TheNumbersOfACutAreHandedOverInTheOneOrderWhateverOrderItsFormHeldThemInTest {

    private static final NumericTerm FIRST = new NumericTerm.ValueOf(TermPath.of("a"));

    private static final NumericTerm SECOND = new NumericTerm.ValueOf(TermPath.of("b"));

    private static final NumericTerm THIRD = new NumericTerm.ValueOf(TermPath.of("c"));

    @Test
    void aCutOverSeveralNumbersHandsThemOverAsTheyAreOrderedAndNotAsItsFormHeldThem() {
        List<NumericTerm> held = List.of(THIRD, FIRST, SECOND);
        List<NumericTerm> reversed = List.of(SECOND, FIRST, THIRD);

        List<NumericTerm> one = List.copyOf(cutHolding(held).terms());
        List<NumericTerm> other = List.copyOf(cutHolding(reversed).terms());

        assertEquals(NumericTerms.inOrder(held), one);
        assertEquals(one, other, "two equal cuts handed a search two sequences");
    }

    private static TakenConstraint.Affine cutHolding(List<NumericTerm> inThatOrder) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (NumericTerm each : inThatOrder) {
            coefs.put(each, ExactRatio.ONE);
        }
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(-2), coefs), Rel.GE);
    }
}
