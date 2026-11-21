package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run stopping at a site has got past is what it works out before it. The right operand of
 * an {@code &&} is worked out only after its left, and has no place of its own, so where the site
 * is in the left it is worked out after the site and is not asked; where it may have been worked
 * out before the site, or where it is not known whether it was, it is.
 */
class ANodeEnteredAfterWhatASiteIsInIsAfterTheSiteTest {

    private static final SourcePos POS = new SourcePos(0, 0);

    private static Core.Int one() {
        return new Core.Int(1, Type.INT, POS);
    }

    private static Core.Binary binary(BinOp op, Core left, Core right) {
        return new Core.Binary(op, left, right, Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.INT, POS);
    }

    /** Whether everything of {@code root} not known to come after {@code site} is accepted, where
     *  {@code refused} is the one node that is not. */
    private static boolean asked(Core root, Core site, Core refused) {
        return EvaluationPlaces.of(root).everyNodeNotAfter(root, site,
                node -> node != refused);
    }

    @Test
    void whatIsEnteredAfterTheOperandTheSiteIsInIsNotAsked() {
        Core.Binary site = binary(BinOp.ADD, one(), one());
        Core.Binary entered = binary(BinOp.ADD, one(), one());
        Core root = binary(BinOp.AND, binary(BinOp.GT, site, one()), entered);
        assertTrue(asked(root, site, entered));
    }

    @Test
    void whatIsEnteredAfterAnOperandDeepAroundTheSiteIsNotAskedEither() {
        Core.Binary site = binary(BinOp.ADD, one(), one());
        Core.Binary entered = binary(BinOp.ADD, one(), one());
        Core left = binary(BinOp.ADD, binary(BinOp.MUL, site, one()), one());
        Core root = binary(BinOp.OR, left, entered);
        assertTrue(asked(root, site, entered));
    }

    @Test
    void whatIsEnteredBeforeTheSiteIsAsked() {
        Core.Binary site = binary(BinOp.ADD, one(), one());
        Core.Binary entered = binary(BinOp.ADD, one(), one());
        Core root = binary(BinOp.ADD, binary(BinOp.AND, one(), entered), site);
        assertFalse(asked(root, site, entered),
                "on the runs where the left of the && holds it is worked out before the site");
    }

    @Test
    void whatIsAskedWhereTheSiteIsInWhatIsEnteredIsEverythingNotKnownToBeAfter() {
        Core.Binary left = binary(BinOp.ADD, one(), one());
        Core.Binary site = binary(BinOp.ADD, one(), one());
        Core root = binary(BinOp.AND, left, binary(BinOp.GT, site, one()));
        assertFalse(asked(root, site, left),
                "the site has no place, and what is not known to be after it may be before");
    }
}
