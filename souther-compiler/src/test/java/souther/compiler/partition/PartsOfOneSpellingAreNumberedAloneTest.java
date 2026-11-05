package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;

/**
 * A statement read at a row numbers its parts once, so that parts spelled alike are one part
 * however many objects stand for them, and a part spelled differently is another.
 */
class PartsOfOneSpellingAreNumberedAloneTest {

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    @Test
    void twoObjectsSpelledAlikeHaveOneNumberAndADifferentSpellingAnother() {
        Proposition one = atLeast(3);
        Proposition apart = atLeast(3);
        Proposition other = atLeast(4);
        assertNotSame(one, apart);
        AStatementAtARow.Parts parts = AStatementAtARow.Parts.of(new Proposition.All(
                List.of(one, new Proposition.Any(List.of(apart, other)))), Map.of());
        assertEquals(parts.numberOf(one), parts.numberOf(apart));
        assertNotEquals(parts.numberOf(one), parts.numberOf(other));
    }

    /** {@code floorMod(d, 7) >= level}. */
    private static Proposition atLeast(long level) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(D, ExactRatio.ONE);
        Quantity remainder = Quantity.RemainderOfADividend.ofTheInput(FLOOR_MOD,
                new LinearForm<>(ExactRatio.ZERO, coefs), BigInteger.valueOf(7));
        Relation.OneWay<Quantity> one = Relation.OneWay.of(new LinearForm<>(
                ExactRatio.of(-level), Map.of(remainder, ExactRatio.ONE)), Rel.GE);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }
}
