package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a run works out to give a name its value is worked out before any operation over the name,
 * and that is every operation told while the value was read: two of them side by side, as the
 * arguments of a call are, are both before it, and the last told does not stand for the other.
 */
class AnOperationOverANameIsWorkedOutAfterEveryOperationThatGaveItsValueTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingId NAME = new BindingId(new BindingOwner.OfValue("m", "f"), 0);

    private static UndividedByARelation.IntOperation operation() {
        return new UndividedByARelation.IntOperation(LinearForm.constant(ExactRatio.ZERO),
                BigInteger.ZERO, BigInteger.ONE, List.of(), true);
    }

    @Test
    void anOperationOverANameIsAfterEveryOneToldWhileItsValueWasRead() {
        AffineReading.WhatWasTold told = new AffineReading.WhatWasTold();
        told.add(new Core.Int(1, Type.INT, POS), operation());
        told.add(new Core.Int(2, Type.INT, POS), operation());
        told.workedOutToGive(NAME, 0);

        assertEquals(Set.of(0, 1), Set.copyOf(told.workedOutOf(
                List.of(new Core.Read("x", NAME, Type.INT, POS)))));
    }

    /** The answer so far a step of a fold is handed is a name given its value by all that was
     *  told before the step: the seed, the elements and the steps before. */
    @Test
    void anOperationOverTheAnswerSoFarIsAfterEveryOneToldBeforeTheStep() {
        AffineReading.WhatWasTold told = new AffineReading.WhatWasTold();
        told.add(new Core.Int(1, Type.INT, POS), operation());
        told.add(new Core.Int(2, Type.INT, POS), operation());
        told.after(NAME);

        assertEquals(Set.of(0, 1), Set.copyOf(told.workedOutOf(
                List.of(new Core.Read("x", NAME, Type.INT, POS)))));
    }

    @Test
    void whatWasToldBeforeTheValueWasReadIsNotWhatGaveIt() {
        AffineReading.WhatWasTold told = new AffineReading.WhatWasTold();
        told.add(new Core.Int(1, Type.INT, POS), operation());
        told.workedOutToGive(NAME, 1);

        assertEquals(List.of(), told.workedOutOf(
                List.of(new Core.Read("x", NAME, Type.INT, POS))));
    }
}
