package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.Placement;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.WhatARelationLeavesUndivided.Told;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.source.SourceId;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import java.math.BigInteger;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
        both.aStopWhereNoRowIs(quotient(), null);
        assertTrue(both.working().leavesUntoldBeyond(List.of(q)));

        AffineReading.WhatWasTold absorbing = new AffineReading.WhatWasTold();
        absorbing.ownStopOfAQuotientByAValueUntold(q);
        AffineReading.WhatWasTold apart = new AffineReading.WhatWasTold();
        apart.aStopWhereNoRowIs(quotient(), null);
        absorbing.absorb(apart);
        assertTrue(absorbing.working().leavesUntoldBeyond(List.of(q)));
    }

    /** A node written at {@code token} of an unnamed text. */
    private static Core at(int token) {
        return new Core.Int(1, Type.INT, new SourcePos(token, 0));
    }

    /** A quotient written at {@code token} of an unnamed text. */
    private static Core.Binary quotientAt(int token) {
        SourcePos pos = new SourcePos(token, 0);
        return new Core.Binary(BinOp.DIV, new Core.Int(1, Type.INT, pos),
                new Core.Int(2, Type.INT, pos), Core.BinaryReading.AS_THEY_STAND,
                ConstructOccurrence.unwritten(), Type.RATIONAL, pos);
    }

    /**
     * Where a stop is left untold is told of what is left once the quotients asked account for
     * theirs, and never of a stop they account for: a quotient written before another stop, and
     * asked, is not the place told; not asked, it is, being written first.
     */
    @Test
    void thePlaceToldIsOneOfWhatTheQuotientsAskedLeave() {
        Core.Binary q = quotientAt(1);
        Core c = at(2);
        AffineReading.WhatWasTold both = new AffineReading.WhatWasTold();
        both.ownStopOfAQuotientByAValueUntold(q);
        both.aStopWhereNoRowIs(c, null);
        NotAccountedFor left = both.working().leftUntold();

        assertTrue(both.working().leavesUntoldBeyond(List.of(q)));
        assertEquals(Optional.of(c), left.whereUnaccountedFor(List.of(q)));
        assertEquals(Optional.of(q), left.whereUnaccountedFor(List.of()));
        AffineReading.WhatWasTold onlyTheQuotient = new AffineReading.WhatWasTold();
        onlyTheQuotient.ownStopOfAQuotientByAValueUntold(q);
        assertEquals(Optional.empty(),
                onlyTheQuotient.working().leftUntold().whereUnaccountedFor(List.of(q)));
    }

    /** Some operation left untold, and a stop left untold at {@code node}. */
    private static UndividedByARelation.Working leavingAStopAt(Core node) {
        return new UndividedByARelation.Working(List.of(), Told.SOME, true, List.of(), true,
                NotAccountedFor.aStopAt(node, null));
    }

    /** Where a reading left a stop untold is kept by the readings together, whether or not they
     *  agree on what they tell, and by whatever a working is put beside or read past; and the
     *  place told of several is the same whatever order they were put together in. */
    @Test
    void whereAReadingLeftAStopUntoldIsKeptByEveryWayOfPuttingWorkingsTogether() {
        Core here = at(1);
        Core there = at(2);
        UndividedByARelation.Working leaving = leavingAStopAt(here);
        // Told of every operation where the other is told of some: the two disagree on what
        // they tell, and are put together as no reading.
        UndividedByARelation.Working toldWhole = new UndividedByARelation.Working(List.of(),
                Told.EVERY);

        assertEquals(Optional.of(here), UndividedByARelation.Working.together(
                List.of(toldWhole, leaving)).leftUntold().whereUnaccountedFor(List.of()));
        assertEquals(Optional.of(here), UndividedByARelation.Working.together(
                List.of(leaving, leavingAStopAt(there))).leftUntold().whereUnaccountedFor(
                        List.of()));
        assertEquals(Optional.of(here), UndividedByARelation.Working.together(
                List.of(leavingAStopAt(there), leaving)).leftUntold().whereUnaccountedFor(
                        List.of()));
        assertEquals(Optional.of(here), leaving.after(aStopNothingAnswersFor()).leftUntold()
                .whereUnaccountedFor(List.of()));
        assertEquals(Optional.of(here), aStopNothingAnswersFor().after(leaving).leftUntold()
                .whereUnaccountedFor(List.of()));
        assertEquals(Optional.of(here),
                leaving.notOnEveryRun().leftUntold().whereUnaccountedFor(List.of()));
    }

    /** Two places at one place of two texts are two places, and putting them together keeps the
     *  same answer in either order: which is told turns on no order of putting together. */
    @Test
    void placesInTwoTextsAreToldTheSameWhicheverIsPutTogetherFirst() {
        Core inOne = new Core.Int(1, Type.INT,
                Placement.aFileOfThisCompile(new SourceId("one")).at(0, 0));
        Core inAnother = new Core.Int(1, Type.INT,
                Placement.aFileOfThisCompile(new SourceId("another")).at(0, 0));
        NotAccountedFor oneFirst = NotAccountedFor.aStopAt(inOne, null)
                .join(NotAccountedFor.aStopAt(inAnother, null));
        NotAccountedFor anotherFirst = NotAccountedFor.aStopAt(inAnother, null)
                .join(NotAccountedFor.aStopAt(inOne, null));

        assertEquals(oneFirst, anotherFirst);
        assertEquals(oneFirst.whereUnaccountedFor(List.of()),
                anotherFirst.whereUnaccountedFor(List.of()));
        assertTrue(oneFirst.whereUnaccountedFor(List.of()).isPresent());
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
