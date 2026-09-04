package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ContainersAddingUp.Repertoire;
import souther.compiler.partition.ContainersAddingUp.Spending;
import souther.compiler.partition.ContainersAddingUp.WhatWasLeft;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The two ends a bounded walk has, and what each of them leaves.
 *
 * <p>A walk that was handed a piece its consumer had no room for stopped at a figure: raise it and
 * that piece gets tried. A walk that ran out of pieces stopped at nothing, and whether anything is
 * left of that kind is a fact about where the pieces came from — so a repertoire that was some of
 * them leaves work nobody did, and one that was all of them leaves none.
 *
 * <p><b>Both, because the walk that decides them cannot tell them apart afterwards.</b> The number
 * of pieces handed over and the figure are the same two numbers whichever end the walk came to, and
 * a reader working out which happened from a subtraction would call every bounded walk a stop. That
 * is what leaves a total nothing composes a container for reported as one this compiler declined to
 * look for.
 *
 * <p>Put to the mechanism rather than through a model. Which member the figure is says nothing here:
 * what is being asked is what a walk records, and a walk records what it was left with.
 */
class AWalkThatRanOutOfPiecesIsNotAWalkThatWasStoppedTest {

    /** The figure the consumer below has room up to, which it reads rather than holding a copy. */
    private static final CompositionBudget FIGURE =
            CompositionBudget.DECOMPOSITIONS_OF_A_TOTAL_OFFERED;

    /** As many pieces as {@link #FIGURE} leaves room for, and no piece refused for anything else. */
    private static final class AsManyAsTheFigure implements Spending<Integer> {

        private int done;

        @Override
        public Taken take(Integer each) {
            if (done == figure().maximum()) {
                return Taken.NOT_TAKEN;
            }
            done++;
            return Taken.AND_MORE;
        }

        @Override
        public CompositionBudget figure() {
            return FIGURE;
        }
    }

    /** Every piece of everything there is, taken: nothing refused and nothing left over. */
    @Test
    void aWalkThroughEverythingThereIsLeavesNothing() {
        WhatWasLeft left = new WhatWasLeft();

        Traversal walked = ContainersAddingUp.asFarAs(upTo(FIGURE.maximum()),
                new AsManyAsTheFigure(), Repertoire.ALL_THERE_ARE, left);

        assertEquals(Traversal.EXHAUSTED, walked, "the pieces ran out before the figure did");
        assertEquals(Set.of(), left.refused(),
                "so no piece was in front of the walk for the figure to have no room for");
        assertEquals(Set.of(), left.heldBack(),
                "and the pieces were everything of their kind, so nothing of it went undone");
    }

    /**
     * The same walk over some of them, which leaves the kind of work it never saw.
     *
     * <p>The one difference is where the pieces came from. A consumer answering this would be
     * answering for a caller it cannot see, and the walk would be recording the arrangement it was
     * set up in rather than what it did.
     */
    @Test
    void aWalkThroughSomeOfThemLeavesWhatItNeverSaw() {
        WhatWasLeft left = new WhatWasLeft();

        Traversal walked = ContainersAddingUp.asFarAs(upTo(FIGURE.maximum()),
                new AsManyAsTheFigure(), Repertoire.SOME_OF_THEM, left);

        assertEquals(Traversal.EXHAUSTED, walked, "the pieces ran out before the figure did");
        assertEquals(Set.of(), left.refused(),
                "nothing was refused, so nothing here is a composing this compiler stopped");
        assertEquals(Set.of(FIGURE), left.heldBack(),
                "and the offer is short of what a piece of that kind would have added, which is"
                        + " what a reader deciding whether everything was tried is owed");
    }

    /**
     * One piece past the figure, which is the figure refusing something that was there.
     *
     * <p>The piece was in front of the walk, so raising the figure tries it. Nothing is recorded of
     * a walk running out, because this one did not: the pieces were still coming.
     */
    @Test
    void aPieceThereWasNoRoomForIsTheFigureDecliningToGoOn() {
        WhatWasLeft left = new WhatWasLeft();

        Traversal walked = ContainersAddingUp.asFarAs(upTo(FIGURE.maximum() + 1),
                new AsManyAsTheFigure(), Repertoire.ALL_THERE_ARE, left);

        assertEquals(Traversal.STOPPED, walked, "a piece was in front of it and was not done");
        assertEquals(Set.of(FIGURE), left.refused(),
                "which is the figure declining to go on, and is what a reader raises");
        assertEquals(Set.of(FIGURE), left.heldBack(),
                "and it is one of the things the offer leaves out, as everything refused is");
    }

    /**
     * A piece that repeats is not a piece there was no room for.
     *
     * <p>What the figure counts is what a reader is handed. A walk that met the figure on a repeat
     * would name it having refused nothing, which is the reading this whole arrangement is against.
     */
    @Test
    void aContainerAlreadyOfferedIsNotAContainerRefused() {
        ContainersAddingUp.WhatIsOffered offered = new ContainersAddingUp.WhatIsOffered();
        WhatWasLeft left = new WhatWasLeft();
        List<FixtureTemplate> filling = distinct(offered.figure().maximum());

        assertEquals(Traversal.EXHAUSTED,
                ContainersAddingUp.asFarAs(filling, offered, Repertoire.ALL_THERE_ARE, left),
                "as many containers as are offered is what is offered");
        assertEquals(Traversal.EXHAUSTED,
                ContainersAddingUp.asFarAs(List.of(filling.get(0)), offered,
                        Repertoire.ALL_THERE_ARE, left),
                "and one already offered is nothing this had to make room for");
        assertEquals(Set.of(), left.heldBack(),
                "so nothing was held back, whatever the offer is full of");

        assertEquals(Traversal.STOPPED,
                ContainersAddingUp.asFarAs(distinct(offered.figure().maximum() + 1), offered,
                        Repertoire.ALL_THERE_ARE, left),
                "and one that is not already offered is a container there is no room for");
        assertEquals(Set.of(CompositionBudget.SHAPES_OF_A_TOTAL_OFFERED), left.refused(),
                "which is the figure over how many are offered, declining to offer another");
    }

    /** The whole numbers below {@code many}, which is a piece of nothing in particular. */
    private static List<Integer> upTo(int many) {
        List<Integer> pieces = new ArrayList<>();
        for (int each = 0; each < many; each++) {
            pieces.add(each);
        }
        return List.copyOf(pieces);
    }

    /** That many values no two of which are the same. */
    private static List<FixtureTemplate> distinct(int many) {
        List<FixtureTemplate> values = new ArrayList<>();
        for (int each = 0; each < many; each++) {
            values.add(FixtureTemplate.string("x".repeat(each + 1)));
        }
        return List.copyOf(values);
    }
}
