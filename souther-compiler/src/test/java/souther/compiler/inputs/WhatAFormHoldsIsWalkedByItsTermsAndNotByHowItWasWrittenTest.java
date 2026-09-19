package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A form is its terms and their coefficients, and walking it is walking those.
 *
 * <p>{@code 6 * b + 3 * a} and {@code 3 * a + 6 * b} are one form. The mapping that holds it says
 * so — what it is equal to is which coefficient stands at which term — and says nothing about which
 * of them was written first. A reader taking the terms off that mapping is reading the order they
 * were put in, and no reader comparing two forms can see any difference between one that was put in
 * either way. So two readers of one form can disagree about which term comes first, and a reader
 * can disagree with itself after a rewrite that changed nothing.
 *
 * <p>What is checked here is that the two orders come out as one, and that putting them in one
 * order never puts two terms under one name.
 */
class WhatAFormHoldsIsWalkedByItsTermsAndNotByHowItWasWrittenTest {

    private static NumericTerm at(String head) {
        return new NumericTerm.ValueOf(TermPath.of(head));
    }

    private static final NumericTerm FIRST_WRITTEN = at("b");
    private static final NumericTerm SECOND_WRITTEN = at("a");

    /** The same form each time: what stands at a term goes with the term, not with where it was
     *  written. What the arguments settle is the order the two were put in. */
    private static Map<NumericTerm, BigDecimal> written(NumericTerm one, NumericTerm other) {
        Map<NumericTerm, BigDecimal> form = new LinkedHashMap<>();
        form.put(one, coefficientAt(one));
        form.put(other, coefficientAt(other));
        return form;
    }

    private static BigDecimal coefficientAt(NumericTerm term) {
        return BigDecimal.valueOf(term.equals(FIRST_WRITTEN) ? 6 : 3);
    }

    /** One form written two ways round is walked one way. */
    @Test
    void oneFormWrittenTwoWaysRoundIsWalkedOneWay() {
        Map<NumericTerm, BigDecimal> oneWay = written(FIRST_WRITTEN, SECOND_WRITTEN);
        Map<NumericTerm, BigDecimal> theOther = written(SECOND_WRITTEN, FIRST_WRITTEN);
        assertTrue(oneWay.keySet().equals(theOther.keySet())
                        && !List.copyOf(oneWay.keySet()).equals(List.copyOf(theOther.keySet())),
                "the two hold the same terms and were written in different orders");

        assertEquals(NumericTerms.inOrder(oneWay.keySet()), NumericTerms.inOrder(theOther.keySet()),
                "so the terms come out in one order");
        assertEquals(List.of(SECOND_WRITTEN, FIRST_WRITTEN), NumericTerms.inOrder(oneWay.keySet()),
                "which is the order of what each term is called");
    }

    /** And what stands at each term goes with it. */
    @Test
    void andWhatStandsAtEachTermGoesWithIt() {
        assertEquals(NumericTerms.entriesInOrder(written(FIRST_WRITTEN, SECOND_WRITTEN)),
                NumericTerms.entriesInOrder(written(SECOND_WRITTEN, FIRST_WRITTEN)));
        assertEquals(List.of(Map.entry(SECOND_WRITTEN, BigDecimal.valueOf(3)),
                        Map.entry(FIRST_WRITTEN, BigDecimal.valueOf(6))),
                NumericTerms.entriesInOrder(written(FIRST_WRITTEN, SECOND_WRITTEN)),
                "each coefficient under the term it stands at");
    }

    /**
     * Two terms are never walked as one.
     *
     * <p>What puts a form in an order is a name written for each term, and a name is not what tells
     * two terms apart — a location written as one name and the same location reached a field at a
     * time are two paths and are spelled the same. A walk that took them for one term would hand
     * over one coefficient twice and the other never, and the form would come out a term short with
     * nothing about the arithmetic looking wrong.
     */
    @Test
    void twoTermsWrittenAlikeAreRefusedRatherThanWalkedAsOne() {
        NumericTerm wholeName = at("a.b");
        NumericTerm aFieldAtATime = new NumericTerm.ValueOf(TermPath.of("a").then("b"));
        assertEquals(wholeName.toString(), aFieldAtATime.toString(),
                "the two are written alike");
        assertTrue(!wholeName.equals(aFieldAtATime), "and are not one term");

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> NumericTerms.inOrder(written(wholeName, aFieldAtATime).keySet()));
        assertTrue(refused.getMessage().contains("a.b"), refused.getMessage());
        assertThrows(IllegalStateException.class,
                () -> NumericTerms.entriesInOrder(written(wholeName, aFieldAtATime)),
                "and the same of what stands at them");
    }

    /** The control: one term is one term, and a form holding it once is walked without complaint. */
    @Test
    void andOneTermUnderOneNameIsWalked() {
        assertEquals(List.of(SECOND_WRITTEN),
                NumericTerms.inOrder(List.of(SECOND_WRITTEN)));
        assertEquals(List.of(), NumericTerms.inOrder(List.of()));
    }
}
