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
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Statements of one remainder are taken off a way together, so they are asked together: a number
 * free to meet each of them is free to meet all of them only where some remainder is one all of
 * them leave, and a remainder of the same form moved by another number is another remainder.
 */
class RemainderStatementsOfOneFormAreTakenAwayOnlyTogetherTest {

    private static final NumericTerm A = new NumericTerm.ValueOf(TermPath.of("a"));
    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
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
    void aFormMovedByAnotherNumberIsAnotherRemainder() {
        assertFalse(UndividedByARelation.sameRemainder(
                statement(0, 7, 1, 1), statement(1, 7, 1, 1)));
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
        Quantity.RemainderOfADividend remainder = Quantity.RemainderOfADividend.ofTheInput(
                FLOOR_MOD, new LinearForm<>(ExactRatio.of(shift), coefs),
                BigInteger.valueOf(divisor));
        return new OnAWay(Set.of(TermPath.of("a"), TermPath.of("d")), false, null, null, null,
                OnAWay.PartsLeftAlone.NONE, null,
                new souther.compiler.partition.RowDemand.OnARemainder(remainder,
                        WholeNumberRuns.one(BigInteger.valueOf(low), BigInteger.valueOf(high))));
    }
}
