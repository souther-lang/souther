package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Predicate;

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

    /**
     * What is left once {@code asked} is taken as accounted for and where it is are one answer,
     * over every value the pieces make in every order: where a node held is not accounted for, one
     * is told and it is one that is not; where every node is, none is; and a value is accounted for
     * only where nothing is left. Putting together is the same in either order, with itself, and
     * however grouped, and so is what is told; widening keeps every place; equal values hash
     * alike. Two quotients at one place are two stops, and asking one leaves the other told.
     */
    @Test
    void whatIsLeftAndWhereItIsAreOneAnswerOverEveryValueInEveryOrder() {
        Core.Binary q1 = binary(BinOp.DIV, one(), one());
        Core.Binary q2 = binary(BinOp.DIV, one(), one());
        Core c = one();
        List<NotAccountedFor> pieces = List.of(NotAccountedFor.quotients(List.of(q1)),
                NotAccountedFor.quotients(List.of(q2)), NotAccountedFor.aStopAt(c, null),
                NotAccountedFor.aStopAt(q1, null), NotAccountedFor.NOTHING.andSomethingElse());
        List<List<Core.Binary>> askings = List.of(List.of(), List.of(q1), List.of(q2),
                List.of(q1, q2));
        List<NotAccountedFor> values = new ArrayList<>();
        for (int subset = 0; subset < 1 << pieces.size(); subset++) {
            NotAccountedFor value = NotAccountedFor.NOTHING;
            NotAccountedFor reversed = NotAccountedFor.NOTHING;
            for (int at = 0; at < pieces.size(); at++) {
                if ((subset & 1 << at) != 0) {
                    value = value.join(pieces.get(at));
                    reversed = pieces.get(at).join(reversed);
                }
            }
            assertEquals(value, reversed, "in either order");
            assertEquals(value.hashCode(), reversed.hashCode());
            assertEquals(value, value.join(value), "with itself");
            values.add(value);
        }
        for (NotAccountedFor value : values) {
            for (List<Core.Binary> asked : askings) {
                Optional<Core> told = value.whereUnaccountedFor(asked);
                if (value.isAccountedForBy(asked)) {
                    assertTrue(told.isEmpty(), "nothing is told where nothing is left");
                }
                if (value.join(NotAccountedFor.aStopAt(c, null)).equals(value)) {
                    assertTrue(told.isPresent(), "a place held that nothing accounts for is told");
                }
                // Asked by the node it is: two quotients written alike are equal as values and
                // are two stops.
                told.ifPresent(node -> assertFalse(asked.stream().anyMatch(one -> one == node)
                        && NotAccountedFor.quotients(List.of((Core.Binary) node))
                                .join(value).equals(value) && !value.join(
                                        NotAccountedFor.aStopAt(node, null)).equals(value),
                        "the place told is no stop the quotients asked account for"));
                assertEquals(told, value.andSomethingElse().whereUnaccountedFor(asked),
                        "widening keeps every place");
                for (NotAccountedFor other : values) {
                    assertEquals(value.join(other).whereUnaccountedFor(asked),
                            other.join(value).whereUnaccountedFor(asked),
                            "what is told turns on no order of putting together");
                }
            }
        }
        NotAccountedFor both = NotAccountedFor.quotients(List.of(q1))
                .join(NotAccountedFor.quotients(List.of(q2)));
        assertFalse(both.isAccountedForBy(List.of(q1)));
        assertEquals(Optional.of(q2), both.whereUnaccountedFor(List.of(q1)),
                "two quotients at one place are two stops");
        assertEquals(Optional.of(q1), NotAccountedFor.quotients(List.of(q1))
                .join(NotAccountedFor.aStopAt(q1, null)).whereUnaccountedFor(List.of(q1)),
                "a stop left untold at a quotient for something else is no stop asking it accounts"
                        + " for");
    }

    /** A reading that leaves many stops untold gathers each at the same cost however many it
     *  holds: twenty thousand, gathered and put together, are all held and all told of. */
    @Test
    void manyStopsGatheredAreEachHeldAtTheCostOfOne() {
        NotAccountedFor.Gathered gathered = new NotAccountedFor.Gathered();
        NotAccountedFor.Gathered other = new NotAccountedFor.Gathered();
        List<Core.Binary> asked = new ArrayList<>();
        for (int at = 0; at < 20_000; at++) {
            Core.Binary quotient = binary(BinOp.DIV, one(), one());
            gathered.quotient(quotient);
            other.stopAt(one(), null);
            asked.add(quotient);
        }
        NotAccountedFor quotients = gathered.done();
        assertTrue(quotients.isAccountedForBy(asked));
        NotAccountedFor together = quotients.join(other.done());
        assertFalse(together.isAccountedForBy(asked));
        assertTrue(together.whereUnaccountedFor(asked).isPresent());
    }

    /** A reading of nothing declared, under a name of its own, so that two are two places. */
    private static InputReads aPlace(int name) {
        return InputReads.ofWhatIsDeclared(
                Map.of(new BindingId(new BindingOwner.OfValue("demo", "f"), name), "x"),
                DeclaredInput.NONE);
    }

    /**
     * A stop is no stop only where every place its node was read at is shown to end no run, and a
     * node read where nothing says is kept, whichever order the places were put together in.
     */
    @Test
    void aStopIsLeftOnlyWhereSomePlaceItWasReadAtMayEndARun() {
        Core.Int node = one();
        InputReads safe = aPlace(0);
        InputReads unsafe = aPlace(1);
        Predicate<Denotation> endsNoRunAtTheSafePlace = value -> value.at().equals(safe);
        NotAccountedFor atTheSafePlace = NotAccountedFor.aStopAt(node, safe);
        assertTrue(atTheSafePlace.besideWhatEndsNoRun(endsNoRunAtTheSafePlace)
                .isAccountedForBy(List.of()));
        for (NotAccountedFor both : List.of(
                atTheSafePlace.join(NotAccountedFor.aStopAt(node, unsafe)),
                atTheSafePlace.join(NotAccountedFor.aStopAt(node, null)),
                NotAccountedFor.aStopAt(node, null).join(atTheSafePlace))) {
            assertFalse(both.besideWhatEndsNoRun(endsNoRunAtTheSafePlace)
                    .isAccountedForBy(List.of()), both::toString);
        }
    }
}
