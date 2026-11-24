package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Derivation.HoldsSomethingWhere.Holding;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.LawProposition;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A statement a law leaves unnamed is on neither side where a condition of that side cannot hold,
 * and every reading of a holding says so the same way.
 *
 * <p>The conditions are those of a side and never the statement: that they all hold says nothing
 * of it, so a statement with conditions that may hold is settled by nothing.
 */
class ASideThatCannotHoldTakesAnUnnamedStatementOutOfItInEveryReadingTest {

    private static final LawProposition<DeclaredArgument> PART = new LawProposition.Always<>(true);

    private static Holding standing(long constant, Rel rel) {
        return new Holding.Stands(LinearForm.constant(ExactRatio.of(constant)), rel);
    }

    /** Conditions that cannot hold: {@code -1 >= 0}. */
    private static final Holding CANNOT = standing(-1, Rel.GE);

    /** Conditions that do: {@code 1 >= 0}. */
    private static final Holding DOES = standing(1, Rel.GE);

    private static Holding unnamed(List<Holding> ifHolds, List<Holding> ifDenied) {
        return new Holding.Unnamed(new Holding.Unnamed.Of.ALaw(PART), ifHolds, ifDenied);
    }

    @Test
    void aHoldingSideWithAConditionThatCannotHoldIsASideItIsNotOn() {
        assertEquals(false, LawOverAtoms.settled(unnamed(List.of(DOES, CANNOT), List.of())));
    }

    @Test
    void aDeniedSideWithAConditionThatCannotHoldIsASideItIsNotOn() {
        assertEquals(true, LawOverAtoms.settled(unnamed(List.of(), List.of(DOES, CANNOT))));
    }

    @Test
    void conditionsThatMayHoldSettleNothingOfIt() {
        assertNull(LawOverAtoms.settled(unnamed(List.of(DOES), List.of(DOES))));
        assertNull(LawOverAtoms.settled(unnamed(List.of(), List.of())));
    }

    @Test
    void theDenialOfOneIsTheOtherWayRound() {
        assertEquals(true, LawOverAtoms.settled(
                new Holding.Not(unnamed(List.of(CANNOT), List.of()))));
    }

    /**
     * Which of the ways of a disjunction may hold is asked of {@code settled}, so a way that cannot
     * be the one leaves the other to make its conditions certain — and one that may leaves both.
     */
    @Test
    void aWayThatCannotHoldLeavesTheOtherWayToMakeItsConditionsCertain() {
        Holding cannot = unnamed(List.of(CANNOT), List.of());
        Holding other = unnamed(List.of(DOES), List.of());
        Holding may = unnamed(List.of(DOES), List.of());

        assertEquals(1, LawOverAtoms.certain(new Holding.AnyOf(List.of(cannot, other)), true)
                .size(), "the one that can hold says what it makes certain");
        assertEquals(0, LawOverAtoms.certain(new Holding.AnyOf(List.of(may, standing(1, Rel.GT))),
                true).size(), "two that may hold make nothing certain");
    }
}
