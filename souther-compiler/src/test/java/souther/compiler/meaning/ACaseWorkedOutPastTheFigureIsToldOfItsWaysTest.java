package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.meaning.TheInputsACaseHoldsFor.relation;

/**
 * A case asked whose cases are more ways of choosing one than are taken apart, and every one of
 * which is worked out all the same, is told of by how many ways it was, beside the cases that
 * were: what asking it cost, which is no stop and says nothing against the line.
 *
 * <p>The ways the choices stand and the ways the numbers leave are two counts. Choices on one
 * number whose comparisons each refute the others leave a few ways of many, and choices on
 * numbers of their own leave as many as they stand.
 */
class ACaseWorkedOutPastTheFigureIsToldOfItsWaysTest {

    private static Quantity number(int at) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("x" + at)));
    }

    /** Held together, {@code choices} choices each between a number being at least a threshold
     *  and being below it: two to the {@code choices} ways as they stand. */
    private static DecidingCase.Cases choices(int choices, boolean ofOneNumber) {
        List<DecidingCase.Cases> each = new ArrayList<>();
        for (int at = 0; at < choices; at++) {
            Quantity of = number(ofOneNumber ? 0 : at);
            each.add(new DecidingCase.Cases.EachOf(List.of(
                    new DecidingCase.Cases.One(relation(Map.of(of, 1), -at, Rel.GE, true)),
                    new DecidingCase.Cases.One(relation(Map.of(of, 1), -at, Rel.GE, false)))));
        }
        return DecidingCase.Cases.together(each);
    }

    private static CasesOfALineAsked.Found asked(DecidingCase.Cases cases) {
        return CasesOfALineAsked.casesOf(new DecidingCase(
                relation(Map.of(number(0), 1), 0, Rel.GE, true), cases),
                _ -> CasesOfALineAsked.Crossing.MAY_CROSS);
    }

    @Test
    void choicesPastTheFigureThatTheNumbersLeaveFewWaysOfAreWorkedOutAndTold() {
        CasesOfALineAsked.Found found = asked(choices(10, true));

        assertTrue(found.notWorkedOutIn().isEmpty(), "no stop");
        assertEquals(1, found.walkedPast().size());
        assertEquals(new CaseCount.Ways.Exactly(BigInteger.valueOf(1024)),
                found.walkedPast().getFirst().counted().structuralWays());
    }

    @Test
    void choicesWithinTheFigureAreWorkedOutAndNotTold() {
        CasesOfALineAsked.Found found = asked(choices(4, true));

        assertTrue(found.notWorkedOutIn().isEmpty());
        assertTrue(found.walkedPast().isEmpty(), "sixteen ways are no more than are taken apart");
    }

    @Test
    void choicesPastTheFigureThatTheNumbersLeaveAsManyWaysOfAreStoppedAndNotToldAsWalked() {
        CasesOfALineAsked.Found found = asked(choices(10, false));

        assertEquals(1, found.notWorkedOutIn().size(), "stopped at the figure");
        assertTrue(found.walkedPast().isEmpty(), "and what was stopped was not walked");
    }
}
