package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.BinOp;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What term each of the six ways to compare two values is named by.
 *
 * <p>A fact is settled by the term it is about, so two clauses comparing the same two values have
 * to name one term however the author reached for the comparison. Six terms for six spellings would
 * leave a guard written one way and a clause written the other talking about different values.
 *
 * <p><b>The terms themselves, written out.</b> What is fixed here is which term each spelling comes
 * to and not that the six come to fewer than six: a reading that answered one term for all of them
 * would satisfy the second and be wrong. So each row says what is built, down to which side of the
 * order each operand is on and whether the term is a denial.
 */
class TwoWritingsOfOneComparisonAreOneTermTest {

    private final Term.Interner interned = new Term.Interner();

    private final Term one = interned.written(1L);

    private final Term two = interned.written(2L);

    /** What each comparison of {@code 1} against {@code 2} is named by. */
    private static Map<BinOp, String> named() {
        Map<BinOp, String> out = new LinkedHashMap<>();
        out.put(BinOp.EQ, "(1 == 2)");
        out.put(BinOp.NE, "!(1 == 2)");
        out.put(BinOp.LT, "(1 LT 2)");
        out.put(BinOp.GE, "!(1 LT 2)");
        out.put(BinOp.GT, "(2 LT 1)");
        out.put(BinOp.LE, "!(2 LT 1)");
        return out;
    }

    private Term comparing(BinOp op) {
        return comparing(op, one, two);
    }

    private Term comparing(BinOp op, Term left, Term right) {
        return interned.comparison(placed(op).canonical(left, right));
    }

    private static ComparisonClaim placed(BinOp op) {
        return (ComparisonClaim) ComparisonPlacement.of(op);
    }

    @Test
    void eachComparisonIsNamedByTheCanonicalTermItStates() {
        Map<BinOp, String> built = new LinkedHashMap<>();
        named().keySet().forEach(op -> built.put(op, comparing(op).rendered()));

        assertEquals(named(), built,
                "the term a comparison is named by is what everything said about it is filed"
                        + " under, so a spelling that comes to a different one is a spelling"
                        + " nothing else can meet");
    }

    @Test
    void anOrderWrittenEitherWayRoundIsOneTerm() {
        assertEquals(comparing(BinOp.LT, one, two), comparing(BinOp.GT, two, one),
                "a < b and b > a state one thing");
        assertEquals(comparing(BinOp.LE, one, two), comparing(BinOp.GE, two, one),
                "a <= b and b >= a state one thing");
    }

    /**
     * And the operator has no way in.
     *
     * <p>Where a comparison could also be named from the operator it was written with, the six
     * would come to what they state twice: once from what the comparison placed, and once here from
     * an operator read below the point where that was settled. The two agree only for as long as
     * somebody keeps them so.
     */
    @Test
    void anOperatorCannotNameWhatAComparisonStates() {
        for (BinOp op : BinOp.values()) {
            if (!op.compares()) {
                continue;
            }
            assertThrows(IllegalArgumentException.class, () -> interned.operator(op, one, two),
                    "what a comparison states is not read off the operator: " + op);
        }
    }

    @Test
    void anEqualityWrittenEitherWayRoundIsOneTerm() {
        assertEquals(comparing(BinOp.EQ, one, two), comparing(BinOp.EQ, two, one),
                "which side of an equality a value was written on says nothing about it");
        assertEquals(comparing(BinOp.NE, one, two), comparing(BinOp.NE, two, one),
                "nor about its denial");
    }
}
