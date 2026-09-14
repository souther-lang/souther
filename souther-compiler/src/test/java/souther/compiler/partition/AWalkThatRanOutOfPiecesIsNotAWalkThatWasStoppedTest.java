package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.partition.ContainersAddingUp.Ends;
import souther.compiler.partition.ContainersAddingUp.Spending;
import souther.compiler.partition.ContainersAddingUp.WhatWasLeft;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two ends a bounded walk has, and what each of them leaves.
 *
 * <p>A walk that was handed a piece its consumer had no room for stopped at a figure: raise it and
 * that piece gets tried. A walk that ran out of pieces stopped at nothing, and a figure recorded
 * there is one that took nothing away from anybody.
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
            CompositionBudget.SHAPES_OF_A_TOTAL_OFFERED;

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

    /** Every piece taken and none left: nothing refused, so no figure is anybody's to raise. */
    @Test
    void aWalkThatRanOutOfPiecesRecordsNoFigure() {
        WhatWasLeft left = new WhatWasLeft();

        Traversal walked = ContainersAddingUp.asFarAs(upTo(FIGURE.maximum()),
                new AsManyAsTheFigure(), left);

        assertEquals(Traversal.EXHAUSTED, walked, "the pieces ran out before the figure did");
        assertEquals(Set.of(), left.refused(),
                "so no piece was in front of the walk for the figure to have no room for");
    }

    /**
     * One piece past the figure, which is the figure refusing something that was there.
     *
     * <p>The piece was in front of the walk, so raising the figure tries it.
     */
    @Test
    void aPieceThereWasNoRoomForIsTheFigureDecliningToGoOn() {
        WhatWasLeft left = new WhatWasLeft();

        Traversal walked = ContainersAddingUp.asFarAs(upTo(FIGURE.maximum() + 1),
                new AsManyAsTheFigure(), left);

        assertEquals(Traversal.STOPPED, walked, "a piece was in front of it and was not done");
        assertEquals(Set.of(FIGURE), left.refused(),
                "which is the figure declining to go on, and is what a reader raises");
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
                ContainersAddingUp.asFarAs(filling, offered, left),
                "as many containers as are offered is what is offered");
        assertEquals(Traversal.EXHAUSTED,
                ContainersAddingUp.asFarAs(List.of(filling.get(0)), offered, left),
                "and one already offered is nothing this had to make room for");
        assertEquals(Set.of(), left.refused(),
                "so nothing was refused, whatever the offer is full of");

        assertEquals(Traversal.STOPPED,
                ContainersAddingUp.asFarAs(distinct(offered.figure().maximum() + 1), offered, left),
                "and one that is not already offered is a container there is no room for");
        assertEquals(Set.of(CompositionBudget.SHAPES_OF_A_TOTAL_OFFERED), left.refused(),
                "which is the figure over how many are offered, declining to offer another");
    }

    /**
     * Whether any arrangement of a given many reaches the total, which is what a claim of having
     * written every arrangement rests on.
     *
     * <p>The elements start at nought and run to two, so two of them reach four and no more. What
     * this is for is the counts where the shapes this compiler writes are every arrangement there
     * is by there being none — and a total past the ends is one no arrangement comes to, whichever
     * way the difference is spread.
     */
    @Test
    void aTotalPastWhereEveryElementCanReachIsReachedByNoArrangement() {
        Ends ends = new Ends(BigDecimal.ZERO, BigDecimal.ZERO, BigDecimal.valueOf(2),
                NumericDomain.Bounds.OPEN);

        assertTrue(ends.reaches(BigDecimal.valueOf(4), 2),
                "two elements of two come to four, so an arrangement of two reaches it");
        assertFalse(ends.reaches(BigDecimal.valueOf(5), 2),
                "and nothing two of them do comes to five, so there is no arrangement to have"
                        + " written");
        assertTrue(ends.reaches(BigDecimal.valueOf(5), 3),
                "a third element reaches it, which is a count of its own");
    }

    /** An order open the way an element would have to move puts nothing in the way of a total. */
    @Test
    void anOrderOpenTheWayAnElementMovesReachesAnything() {
        Ends open = new Ends(BigDecimal.ZERO, BigDecimal.ZERO, null, NumericDomain.Bounds.OPEN);

        assertTrue(open.reaches(BigDecimal.valueOf(1_000_000), 1),
                "nothing names a value this element cannot be moved up to");
        assertFalse(open.reaches(BigDecimal.valueOf(-1), 1),
                "and the end it would move down to is named, and is where it starts");
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
