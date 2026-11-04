package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two histories of choices come to one state ({@link ResidualState#of}) only where what they chose
 * leaves the same question for every case still to choose: where a fact is eliminated, what it
 * leaves behind is held whole, and a fact nothing reads exactly is held as it was said.
 */
class TwoHistoriesShareAStateOnlyWhereTheyLeaveTheSameQuestionTest {

    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    private static final TermPath HOLIDAYS = TermPath.of("holidays");
    private static final Quantity HOLIDAY =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(HOLIDAYS.element()));
    private static final Quantity FROM =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("from")));
    private static final Quantity X =
            new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("x")));

    private static Optional<Set<Object>> stateOf(Proposition... chosen) {
        return ResidualState.of(List.of(chosen), List.of(), _ -> Set.of(), Set.of(), _ -> true);
    }

    /**
     * A date said to be among the holidays leaves that it is a date: the base moved by it is
     * within the dates. Dates on both sides of the base are held at both ends, so a history
     * reaching further below the base is not the one that reaches less far, and one reaching no
     * further either way is.
     */
    @Test
    void datesOnBothSidesOfTheBaseAreHeldAtBothEnds() {
        Optional<Set<Object>> oneBelow = stateOf(aHoliday(2), aHoliday(-1));
        assertTrue(oneBelow.isPresent(), "the holidays are held to nothing, and eliminated");
        assertNotEquals(oneBelow, stateOf(aHoliday(2), aHoliday(-2)),
                "a date two below the base is no date where one below is");
        assertNotEquals(oneBelow, stateOf(aHoliday(3), aHoliday(-1)),
                "a date three above the base is no date where two above is");
        assertEquals(oneBelow, stateOf(aHoliday(2), aHoliday(1), aHoliday(-1)),
                "a date between the two ends is a date wherever both are");
    }

    /**
     * A remainder of a form the owner of remainders reads ({@link ARemainderMoved}) is held as the
     * remainders it leaves, whichever statement said them; one it does not read is held as the
     * statement, and two such statements are two states.
     */
    @Test
    void aRemainderTheOwnerDoesNotReadIsHeldAsItWasSaid() {
        assertEquals(stateOf(remainderOf(ExactRatio.ONE, 1, 1)),
                stateOf(remainderOf(ExactRatio.ONE, 0, 0)),
                "floorMod(x + 1, 7) == 1 leaves what floorMod(x, 7) == 0 does");
        ExactRatio half = ExactRatio.of(BigInteger.ONE, BigInteger.TWO);
        assertNotEquals(stateOf(remainderOf(half, 0, 1)), stateOf(remainderOf(half, 0, 2)),
                "remainders of half of x are read by nothing, and say different things");
    }

    /** That some holiday is {@code from} moved by {@code days}. */
    private static Proposition aHoliday(int days) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(HOLIDAY, ExactRatio.ONE);
        coefs.put(FROM, ExactRatio.of(-1));
        return new Proposition.Some(new DecisionSubject.AnInput(HOLIDAYS),
                compared(new LinearForm<>(ExactRatio.of(-days), coefs), Rel.EQ), true);
    }

    /** {@code floorMod(weight·x + moved, 7) == left}. */
    private static Proposition remainderOf(ExactRatio weight, int moved, int left) {
        Quantity remainder = new Quantity.RemainderOfADividend(FLOOR_MOD,
                new LinearForm<>(ExactRatio.of(moved), Map.of(X, weight)), BigInteger.valueOf(7));
        return compared(new LinearForm<>(ExactRatio.of(-left), Map.of(remainder, ExactRatio.ONE)),
                Rel.EQ);
    }

    private static Proposition compared(LinearForm<Quantity> form, Rel rel) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, rel);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }
}
