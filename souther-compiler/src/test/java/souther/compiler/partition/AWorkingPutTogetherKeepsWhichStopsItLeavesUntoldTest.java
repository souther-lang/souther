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

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a working leaves untold is said of which stops those are, and putting workings together
 * keeps every one of them: a stop no
 * reading answers for is not made a quotient's own by being put beside one, two readings that
 * leave different quotients leave both, and an operation told at two nodes is at neither.
 */
class AWorkingPutTogetherKeepsWhichStopsItLeavesUntoldTest {

    private static final SourcePos POS = new SourcePos(0, 0);

    private static Core.Binary quotient() {
        return new Core.Binary(BinOp.DIV, new Core.Int(1, Type.INT, POS),
                new Core.Int(2, Type.INT, POS), Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.RATIONAL, POS);
    }

    /** Every operation told, and a stop left that no reading answers for. */
    private static UndividedByARelation.Working aStopNothingAnswersFor() {
        return new UndividedByARelation.Working(List.of(), Told.EVERY, true, List.of(), true);
    }

    /** Only the stop of {@code q}, a quotient, is left untold. */
    private static UndividedByARelation.Working onlyTheStopOf(Core.Binary q) {
        return new UndividedByARelation.Working(List.of(), Told.SOME, true, List.of(), true,
                NotAccountedFor.quotients(List.of(q)));
    }

    @Test
    void aStopNothingAnswersForIsNotLostBesideAQuotientsOwn() {
        Core.Binary q = quotient();
        UndividedByARelation.Working together =
                onlyTheStopOf(q).after(aStopNothingAnswersFor());
        assertTrue(together.aStopUntold());
        assertTrue(together.leavesUntoldBeyond(List.of(q)),
                "the stop no reading answers for is left untold whichever quotients are asked");
        assertTrue(aStopNothingAnswersFor().after(onlyTheStopOf(q)).leavesUntoldBeyond(List.of(q)));
    }

    @Test
    void aQuotientAskedAccountsForWhatIsLeftToItAndNothingElse() {
        Core.Binary q = quotient();
        assertFalse(onlyTheStopOf(q).leavesUntoldBeyond(List.of(q)));
        assertTrue(onlyTheStopOf(q).leavesUntoldBeyond(List.of(quotient())),
                "a quotient that is not asked is left to something else");
        assertTrue(onlyTheStopOf(q).after(onlyTheStopOf(quotient())).leavesUntoldBeyond(
                List.of(q)));
    }

    @Test
    void twoReadingsLeavingDifferentQuotientsUntoldLeaveBoth() {
        Core.Binary first = quotient();
        Core.Binary second = quotient();
        UndividedByARelation.Working together = UndividedByARelation.Working.together(
                List.of(onlyTheStopOf(first), onlyTheStopOf(second)));
        assertTrue(together.leavesUntoldBeyond(List.of(first)),
                "the second quotient's stop is untold where only the first is asked");
        assertTrue(together.leavesUntoldBeyond(List.of(second)));
        assertFalse(together.leavesUntoldBeyond(List.of(first, second)));
    }

    /** A reading that left a quotient's own stop untold, and then a stop no operation tells, left
     *  the second untold whichever quotients are asked, in whatever order and through whichever
     *  way the two were put into one reading. */
    @Test
    void aReadingThatLeftAQuotientsStopAndAnotherStopUntoldLeavesTheOtherBeyondEveryQuotient() {
        Core.Binary q = quotient();
        AffineReading.WhatWasTold onlyTheQuotient = new AffineReading.WhatWasTold();
        onlyTheQuotient.ownStopOfAQuotientByAValueUntold(q);
        assertFalse(onlyTheQuotient.working().leavesUntoldBeyond(List.of(q)));

        AffineReading.WhatWasTold both = new AffineReading.WhatWasTold();
        both.ownStopOfAQuotientByAValueUntold(q);
        both.aStopWhereNoRowIs();
        assertTrue(both.working().leavesUntoldBeyond(List.of(q)));

        AffineReading.WhatWasTold absorbing = new AffineReading.WhatWasTold();
        absorbing.ownStopOfAQuotientByAValueUntold(q);
        AffineReading.WhatWasTold apart = new AffineReading.WhatWasTold();
        apart.aStopWhereNoRowIs();
        absorbing.absorb(apart);
        assertTrue(absorbing.working().leavesUntoldBeyond(List.of(q)));
    }

    private static UndividedByARelation.IntOperation operationAt(Core node) {
        return new UndividedByARelation.IntOperation(LinearForm.constant(ExactRatio.ONE),
                BigInteger.ZERO, BigInteger.TEN, List.of()).workedOutAt(node);
    }

    @Test
    void anOperationToldAtTwoNodesByTwoReadingsIsAtNeither() {
        Core here = quotient();
        Core there = quotient();
        UndividedByARelation.Working one = new UndividedByARelation.Working(
                List.of(operationAt(here)), Told.EVERY);
        UndividedByARelation.Working another = new UndividedByARelation.Working(
                List.of(operationAt(there)), Told.EVERY);
        assertNull(UndividedByARelation.Working.together(List.of(one, another)).operations()
                .getFirst().origin().node());
        assertSame(here, UndividedByARelation.Working.together(List.of(one, one)).operations()
                .getFirst().origin().node());
    }
}
