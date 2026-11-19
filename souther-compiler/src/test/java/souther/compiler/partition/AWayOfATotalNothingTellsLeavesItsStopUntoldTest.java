package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.WhatARelationLeavesUndivided;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.KeptWays;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run taking a way of keeping the elements of a total works out, as a reading that read the
 * comparison over the total once says it: a way where no run may stop says nothing, and a way no
 * reading tells the total of, one whose working leaves a stop untold though it tells no
 * operation, or ways too many to be written out, leave a stop untold rather than none. Where the
 * stop is told on each way is told exactly where what each way works out is kept.
 */
class AWayOfATotalNothingTellsLeavesItsStopUntoldTest {

    private static final Proposition ANYWHERE = new Proposition.Always(true);

    private static final Core TOTAL = new Core.Int(0, Type.INT, new SourcePos(0, 0));

    /** {@code elements} elements, each kept by a truth of its own, so that there are two ways for
     *  each of them. */
    private static Derivation.WaysWrittenWhenAsked waysOf(int elements) {
        List<List<KeptWays.Keep>> keptBy = new ArrayList<>();
        List<LinearForm<Quantity>> forms = new ArrayList<>();
        for (int i = 0; i < elements; i++) {
            keptBy.add(List.of(new KeptWays.Keep(i, true)));
            forms.add(LinearForm.constant(ExactRatio.of(1L)));
        }
        return new Derivation.WaysWrittenWhenAsked(new KeptWays(keptBy, elements), Map.of(),
                new Derivation.TheRunStopsHere(), forms, new Quantity.TheKeptTotal(1, false),
                Optional.empty(), 0, Map.of(), false);
    }

    private static List<StopEvidence.OnAnArm> onTheWays(
            Derivation.WaysWrittenWhenAsked ways,
            Function<LinearForm<Quantity>, UndividedByARelation.Working> totalOfAWay) {
        Pullback.Trial trial = new Pullback.Trial();
        trial.readOnTheWays(ways, TOTAL, totalOfAWay);
        return trial.onTheWays(ways, ANYWHERE);
    }

    @Test
    void aWayWhereNoRunMayStopSaysNothing() {
        assertEquals(List.of(),
                onTheWays(waysOf(1), _ -> UndividedByARelation.Working.NOTHING));
    }

    @Test
    void aWayWhoseTotalNoReadingTellsLeavesAStopUntold() {
        List<StopEvidence.OnAnArm> said = onTheWays(waysOf(1), _ -> null);
        assertEquals(2, said.size(), "one for each way");
        assertTrue(said.stream().allMatch(each -> each.stops().operations().aStopUntold()),
                "each leaves a stop untold");
    }

    /** A working that tells no operation and leaves a stop untold is a stop, not none. */
    @Test
    void aWayWhoseWorkingLeavesAStopUntoldWithNoOperationSaysSo() {
        UndividedByARelation.Working untold = new UndividedByARelation.Working(List.of(),
                WhatARelationLeavesUndivided.Told.EVERY, true, List.of(), true);
        List<StopEvidence.OnAnArm> said = onTheWays(waysOf(1), _ -> untold);
        assertEquals(2, said.size(), "one for each way");
        assertTrue(said.stream().allMatch(each -> each.stops().operations().aStopUntold()));
    }

    /** Fifteen truths come to more ways than a statement is written out over. */
    @Test
    void waysTooManyToWriteOutLeaveAStopUntoldWhereTheyAreRead() {
        List<StopEvidence.OnAnArm> said = onTheWays(waysOf(15), _ -> {
            throw new AssertionError("no way is taken one by one");
        });
        assertEquals(1, said.size(), "one, where they are read");
        assertSame(ANYWHERE, said.getFirst().reached());
        assertTrue(said.getFirst().stops().operations().aStopUntold());
    }

    /** Told where it is kept, and carried with it to the candidate it is kept under. */
    @Test
    void whereTheStopIsToldGoesWithWhatTellsIt() {
        Pullback.Trial read = new Pullback.Trial();
        read.readOnTheWays(waysOf(1), TOTAL, _ -> UndividedByARelation.Working.NOTHING);
        assertTrue(read.toldWhereItStops(TOTAL));
        Pullback.Trial keeping = new Pullback.Trial();
        keeping.absorb(read);
        assertTrue(keeping.toldWhereItStops(TOTAL));
    }
}
