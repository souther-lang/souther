package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.OnOneElement;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.TheElementComesRound;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.time.Duration;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A statement that holds one part in many places is read once for each part it is made of, and
 * not once for every place a part stands.
 *
 * <p>Statements share their parts — what a search before an element states is held again under
 * every later element — so written out as a tree, one is many times the parts it is made of.
 * Here each level holds the one below twice, as many levels deep as its spelling, which a string
 * holds, lets it be: as a tree that is millions of places, as parts it is a few dozen. What each
 * reading says of it is
 * held against what it says of the first level, which the deeper ones mean the same as.
 */
class AStatementSharingItsPartsIsReadOncePerPartTest {

    private static final NumericTerm D = new NumericTerm.ValueOf(TermPath.of("d"));
    private static final NumericTerm S = new NumericTerm.ValueOf(TermPath.of("s"));
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    /** As deep as a statement goes whose spelling a string still holds. */
    private static final int LEVELS = 21;

    @Test
    void eachReadingWalksADeeplySharedStatementOnceForEachPart() {
        Proposition first = level(remainderAtLeast(0, 2));
        Proposition deep = first;
        for (int at = 1; at < LEVELS; at++) {
            deep = level(deep);
        }
        Proposition shared = deep;
        BigInteger seven = BigInteger.valueOf(7);
        assertTimeoutPreemptively(Duration.ofSeconds(2), () -> {
            assertEquals(ResiduesAStatementLeaves.of(first, form(), seven),
                    ResiduesAStatementLeaves.of(shared, form(), seven),
                    "the deep statement means what the first level does");
            assertTrue(OnOneElement.theElementOf(shared).isEmpty(), "it weighs no element");
            assertTrue(TheElementComesRound.in(shared).isEmpty(),
                    "and so comes round over none");
        });
    }

    /** {@code (below and floorMod(d - s + 1, 7) >= 3) or (below and floorMod(d - s + 2, 7) >= 5)}:
     *  {@code below} held in two places. */
    private static Proposition level(Proposition below) {
        return new Proposition.Any(List.of(
                new Proposition.All(List.of(below, remainderAtLeast(1, 3))),
                new Proposition.All(List.of(below, remainderAtLeast(2, 5)))));
    }

    /** {@code floorMod(d - s + shift, 7) >= level}. */
    private static Proposition remainderAtLeast(long shift, long level) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(D, ExactRatio.ONE);
        coefs.put(S, ExactRatio.of(-1));
        Quantity remainder = Quantity.RemainderOfADividend.ofTheInput(FLOOR_MOD,
                new LinearForm<>(ExactRatio.of(shift), coefs), BigInteger.valueOf(7));
        Relation.OneWay<Quantity> one = Relation.OneWay.of(new LinearForm<>(
                ExactRatio.of(-level), Map.of(remainder, ExactRatio.ONE)), Rel.GE);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }

    private static LinearForm<NumericTerm> form() {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(D, ExactRatio.ONE);
        coefs.put(S, ExactRatio.of(-1));
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }
}
