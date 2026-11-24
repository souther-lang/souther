package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.WholeNumberRuns;
import souther.compiler.partition.UndividedByARelation.OnAWay;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Statements of one remainder are taken off a way together, so they are asked together: a number
 * free to meet each of them is free to meet all of them only where some remainder of the form is
 * one all of them leave. A remainder of the same form moved by another number is the same
 * remainder ({@link ARemainderMoved}), and what it leaves is held against the others turned back
 * by its move.
 */
class RemainderStatementsOfOneFormAreTakenAwayOnlyTogetherTest {

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
    private static final NumericTerm ELEMENT =
            new NumericTerm.ValueOf(TermPath.of("xs").element());
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    @Test
    void statementsThatLeaveNoRemainderBetweenThemAreNotAskedAsOne() {
        assertFalse(UndividedByARelation.allowTogether(List.of(
                statement(0, 7, 1, 1), statement(0, 7, 2, 2))));
    }

    @Test
    void statementsThatLeaveARemainderBetweenThemAreAskedAsOne() {
        assertTrue(UndividedByARelation.allowTogether(List.of(
                statement(0, 7, 1, 3), statement(0, 7, 3, 5))));
    }

    @Test
    void aFormMovedByAnotherNumberIsTheSameRemainder() {
        assertTrue(UndividedByARelation.sameRemainder(
                statement(0, 7, 1, 1), statement(1, 7, 1, 1)));
    }

    /** Six of the form, and one of it moved by two, are both six of the form unmoved; six of it
     *  moved by two is four. */
    @Test
    void statementsMovedApartAreAskedAsOneWhereTheyLeaveARemainderOfTheFormBetweenThem() {
        assertTrue(UndividedByARelation.allowTogether(List.of(
                statement(0, 7, 6, 6), statement(2, 7, 1, 1))));
        assertFalse(UndividedByARelation.allowTogether(List.of(
                statement(0, 7, 6, 6), statement(2, 7, 6, 6))));
    }

    /** A number inside a container may be of another element in each statement. */
    @Test
    void statementsOfANumberInsideAContainerAreNotOneRemainder() {
        Map<NumericTerm, ExactRatio> element = Map.of(ELEMENT, ExactRatio.ONE);
        assertFalse(UndividedByARelation.sameRemainder(
                statement(element, 0, 7, 1, 1), statement(element, 0, 7, 1, 1)));
        assertFalse(UndividedByARelation.allowTogether(List.of(
                statement(element, 0, 7, 1, 1))));
    }

    @Test
    void aFormDividedByAnotherNumberIsAnotherRemainder() {
        assertFalse(UndividedByARelation.sameRemainder(
                statement(0, 7, 1, 1), statement(0, 5, 1, 1)));
    }

    @Test
    void theSameDivisionOfTheSameFormIsOneRemainder() {
        assertTrue(UndividedByARelation.sameRemainder(
                statement(0, 7, 1, 1), statement(0, 7, 2, 2)));
    }

    /** {@code floorMod(a - d + shift, divisor)} held to the remainders from {@code low} to {@code high}. */
    private static OnAWay statement(long shift, long divisor, long low, long high) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(A, ExactRatio.ONE);
        coefs.put(D, ExactRatio.of(-1));
        return statement(coefs, shift, divisor, low, high);
    }

    private static OnAWay statement(Map<NumericTerm, ExactRatio> coefs, long shift, long divisor,
                                    long low, long high) {
        Quantity.RemainderOfADividend remainder = Quantity.RemainderOfADividend.ofTheInput(
                FLOOR_MOD, new LinearForm<>(ExactRatio.of(shift), coefs),
                BigInteger.valueOf(divisor));
        Set<TermPath> positions = new LinkedHashSet<>();
        coefs.keySet().forEach(term -> positions.add(term.subjectPath()));
        return new OnAWay(positions, false, null, null, null, OnAWay.PartsLeftAlone.NONE, null,
                new RowDemand.OnARemainder(remainder,
                        WholeNumberRuns.one(BigInteger.valueOf(low), BigInteger.valueOf(high))));
    }
}
