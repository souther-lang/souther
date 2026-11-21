package souther.compiler.core;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run stopping at a site has not got to what it works out after it: what the site is in, whose
 * own step comes after what it is made of, and what is worked out past it, an arm and the right
 * of an operator that may settle included, which a run enters after what decides it. What may
 * have been worked out before it is not among them, nor is anything where the site is not found
 * once.
 */
class WhatARunHasNotGotToWhereASiteStopsIsFoundInTheOrderItWorksNodesOutTest {

    private static final SourcePos POS = new SourcePos(0, 0);

    private static Core.Int one() {
        return new Core.Int(1, Type.INT, POS);
    }

    private static Core.Binary binary(BinOp op, Core left, Core right) {
        return new Core.Binary(op, left, right, Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.INT, POS);
    }

    private static Set<Core> after(Core root, Core site) {
        return Evaluated.workedOutAfter(List.of(root), site);
    }

    @Test
    void whatTheSiteIsInAndWhatIsWorkedOutPastItAreAfterAndWhatIsBeforeItIsNot() {
        Core.Binary site = binary(BinOp.ADD, one(), one());
        Core.Binary before = binary(BinOp.ADD, one(), one());
        Core.Binary past = binary(BinOp.ADD, one(), one());
        Core.Binary around = binary(BinOp.MUL, before, site);
        Core root = binary(BinOp.ADD, around, past);
        Set<Core> after = after(root, site);
        assertTrue(after.contains(around) && after.contains(root) && after.contains(past));
        assertFalse(after.contains(before) || after.contains(site));
    }

    @Test
    void theRightOfAnOperatorThatMaySettleIsAfterASiteInItsLeftAndMayBeBeforeOneBesideIt() {
        Core.Binary site = binary(BinOp.ADD, one(), one());
        Core.Binary right = binary(BinOp.ADD, one(), one());
        assertTrue(after(binary(BinOp.AND, binary(BinOp.GT, site, one()), right), site)
                .contains(right));
        assertFalse(after(binary(BinOp.ADD, binary(BinOp.AND, one(), right), site), site)
                .contains(right),
                "on the runs where the left holds it is worked out before the site");
    }

    @Test
    void anArmIsAfterASiteInTheConditionAndMayBeBeforeASiteAfterTheChoice() {
        Core.Binary site = binary(BinOp.ADD, one(), one());
        Core.Binary arm = binary(BinOp.ADD, one(), one());
        Core.ForkPlace place = Core.ForkPlace.asWritten(ConstructOccurrence.unwritten());
        Core.If choice = new Core.If(binary(BinOp.GT, site, one()), arm, one(), place, Type.INT,
                POS);
        assertTrue(after(choice, site).contains(arm));
        Core.If other = new Core.If(new Core.Bool(true, Type.BOOL, POS), arm, one(), place,
                Type.INT, POS);
        assertFalse(after(binary(BinOp.ADD, other, site), site).contains(arm));
    }

    @Test
    void nothingIsAfterASiteThatIsNotFoundOnceOrNotAtAll() {
        Core.Binary site = binary(BinOp.ADD, one(), one());
        Core.Binary past = binary(BinOp.ADD, one(), one());
        assertEquals(Set.of(), after(binary(BinOp.ADD, site, site), site),
                "where it is held twice, which of them a run stops at is not known");
        assertEquals(Set.of(), after(binary(BinOp.ADD, past, past), site));
        assertEquals(Set.of(), after(binary(BinOp.ADD, site, past), null));
    }

    /** A node held at many places is not walked once for each: a tree of depth 40 whose every
     *  node holds the one below twice has 2^40 places. */
    @Test
    void aNodeHeldAtManyPlacesIsNotWalkedOnceForEachOfThem() {
        Core node = one();
        for (int depth = 0; depth < 40; depth++) {
            node = binary(BinOp.ADD, node, node);
        }
        Core.Binary site = binary(BinOp.ADD, one(), one());
        assertEquals(Set.of(), after(node, site));
    }
}
