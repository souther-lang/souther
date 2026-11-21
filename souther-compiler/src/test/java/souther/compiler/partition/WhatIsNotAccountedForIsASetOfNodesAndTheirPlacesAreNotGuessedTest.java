package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a working leaves untold is a set of the nodes of quotients, and an operation's place is
 * the node it is worked out at: two of them are equal where they name the same nodes, whichever
 * way they were put together, and a node a run works out more than once has no one place.
 */
class WhatIsNotAccountedForIsASetOfNodesAndTheirPlacesAreNotGuessedTest {

    private static final SourcePos POS = new SourcePos(0, 0);

    private static Core.Int one() {
        return new Core.Int(1, Type.INT, POS);
    }

    private static Core.Binary binary(BinOp op, Core left, Core right) {
        return new Core.Binary(op, left, right, Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.INT, POS);
    }

    @Test
    void twoValuesNamingTheSameNodesAreEqualWhateverTheOrderAndRepeats() {
        Core.Binary first = binary(BinOp.DIV, one(), one());
        Core.Binary second = binary(BinOp.DIV, one(), one());
        NotAccountedFor repeated = NotAccountedFor.quotients(List.of(first, first));
        NotAccountedFor both = NotAccountedFor.quotients(List.of(first, second));
        assertNotEquals(repeated, both);
        assertNotEquals(both, repeated, "equality holds both ways or neither");
        assertEquals(NotAccountedFor.quotients(List.of(first)), repeated);
        assertEquals(both, NotAccountedFor.quotients(List.of(second, first)));
    }

    @Test
    void joiningIsIdempotentAndCommutative() {
        NotAccountedFor first = NotAccountedFor.quotients(List.of(binary(BinOp.DIV, one(), one())));
        NotAccountedFor second =
                NotAccountedFor.quotients(List.of(binary(BinOp.DIV, one(), one())));
        assertEquals(first, first.join(first));
        assertEquals(first.join(second), second.join(first));
        assertEquals(first.join(second).join(first), first.join(second));
    }

    @Test
    void aNodeSharedByTwoPlacesOfTheTreeHasNoPlaceToBeAfterOrBefore() {
        Core.Binary shared = binary(BinOp.ADD, one(), one());
        Core.Binary division = binary(BinOp.DIV, shared, one());
        Core.Binary last = binary(BinOp.ADD, one(), one());
        Core root = binary(BinOp.ADD, binary(BinOp.ADD, division, shared), last);
        EvaluationPlaces places = EvaluationPlaces.of(root);
        assertFalse(places.comesAfter(shared, division),
                "it is worked out before the division as well, as one of its operands");
        assertFalse(places.comesAfter(last, shared) && places.comesAfter(shared, last));
        assertFalse(places.comesAfter(last, shared),
                "where it stands is not known, and nothing is said to be after it");
    }

    private static UndividedByARelation.Working workingWithAnOperationAt(Core node) {
        return new UndividedByARelation.Working(List.of(new UndividedByARelation.IntOperation(
                LinearForm.constant(ExactRatio.ONE), BigInteger.ZERO, BigInteger.TEN, List.of())
                .workedOutAt(node)), Told.EVERY);
    }

    /** That an operation was told asks about the number, whichever node it was told at and
     *  whether it was told here or in a reading taken in. */
    @Test
    void anOperationIsToldOnceWhereverItWasToldAndHoweverItWasTakenIn() {
        UndividedByARelation.IntOperation plain = new UndividedByARelation.IntOperation(
                LinearForm.constant(ExactRatio.ONE), BigInteger.ZERO, BigInteger.TEN, List.of());
        Core node = binary(BinOp.ADD, one(), one());
        AffineReading.WhatWasTold here = new AffineReading.WhatWasTold();
        here.add(node, plain);
        assertTrue(here.told(plain));
        assertTrue(here.told(plain.workedOutAt(binary(BinOp.ADD, one(), one()))));

        AffineReading.WhatWasTold apart = new AffineReading.WhatWasTold();
        apart.add(node, plain);
        AffineReading.WhatWasTold taking = new AffineReading.WhatWasTold();
        taking.absorb(apart);
        assertTrue(taking.told(plain));
    }

    @Test
    void twoWorkingsThatTellOneOperationAtDifferentNodesAreNotEqual() {
        Core here = binary(BinOp.ADD, one(), one());
        Core there = binary(BinOp.ADD, one(), one());
        assertEquals(workingWithAnOperationAt(here), workingWithAnOperationAt(here));
        assertNotEquals(workingWithAnOperationAt(here), workingWithAnOperationAt(there));
    }
}
