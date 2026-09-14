package souther.compiler.partition;

import souther.compiler.numeric.Towards;

import java.util.ArrayList;
import java.util.List;

/**
 * Which levels of one coverage item a search is offered, in what order, and how many.
 *
 * <p><b>All policy and no meaning.</b> Which values stand at an item is the item's
 * ({@link Criterion#region}), and what an order has among them is the order's
 * ({@link LevelSpace#inspect}); neither of them says which to look at first, and neither should. A
 * class of everything but one value leaves the run under it and the run over it, and nothing about
 * those two sets says which one a reader should be handed — so the choice is made here, where it can
 * be read as a choice.
 *
 * <p>Apart from {@link LevelRealizer} because the two answer different questions. This says which
 * levels are worth trying; that one says whether a row can be composed at one. Held together, the
 * budget for looking sat next to the arithmetic that solves a form, and how far to look read like a
 * fact about the order rather than about how long this compiler is willing to spend.
 *
 * <p>Two rules, and both are choices rather than consequences. A level always comes out of what the
 * item leaves after everything already offered, so the walk cannot leave the item however long it
 * runs. And it walks <em>away from the line</em>: the point inside a partition exists to be beside
 * its boundary, so the first level offered is the one nearest the line the point is named for and
 * not the one furthest from it.
 */
public final class LevelCandidateSource {

    /**
     * How many levels of one item are tried before the search gives up on it.
     *
     * <p>A run is met anywhere in it, so the first level a row can be written at stands for the whole
     * of it; a box that holds none of the first few holds one only where the rules are shaped so that
     * the whole search is worth its own answer.
     */
    private static final int LEVELS_TRIED =
            CompositionBudget.LEVELS_A_SIDE_IS_ASKED_AT.maximum();

    /**
     * The levels a row at this item could stand at, nearest the line first.
     *
     * <p>A point stands at one level and nowhere else — a level further out is a different point of
     * the border, and offering it would answer a question nobody asked. A run is met anywhere in it,
     * and a class of everything but one value at either of the two sides of it, so both are asked
     * for outward from what they are written against until the budget runs out. Which is why a run
     * that came back empty settles nothing while a point may.
     */
    public static Offered forItem(Criterion where, LevelSpace levels) {
        Level from = where.anchor();
        return switch (where) {
            case Criterion.AtTheLevel _ -> new Offered(List.of(from), false);
            case Criterion.Within within -> inside(levels, within);
        };
    }

    /**
     * The levels offered, and whether there were more this stopped short of.
     *
     * <p>Two halves of one answer. A caller reading only the first says the levels are all the
     * levels there were, which is what a run whose far end nothing reached looks like from here —
     * and the difference is whether raising a figure of this compiler's would offer more.
     */
    public record Offered(List<Level> levels, boolean stoppedShort) {

        public Offered {
            levels = List.copyOf(levels);
        }
    }

    /**
     * The levels of a run a row could stand at, from the line inward.
     *
     * <p>The value against the line is the one level of the run that will not do, so the search
     * starts there and walks away from it, which is the direction the point is named for. Walked
     * from the run's far end instead, a row well inside a wide run was offered where one just inside
     * it says the same thing and is the row an author would have written.
     */
    private static Offered inside(LevelSpace levels, Criterion.Within within) {
        Level from = within.anchor();
        if (from == null) {
            return new Offered(List.of(), false);
        }
        List<Level> out = new ArrayList<>();
        if (within.holds(from)) {
            out.add(from);
        }
        Offered drawn = drawnFrom(levels, within.region(), from, within.away());
        out.addAll(drawn.levels());
        return new Offered(out, drawn.stoppedShort());
    }

    /**
     * Levels of {@code region} to try, walking away from {@code from}.
     *
     * <p>Each one is asked for inside what is left, which is the region less everything already
     * offered — so a level always comes from the item itself and the walk can never leave it, and
     * two of them are never the same level. Stepped outward from the anchor instead, a step was as
     * coarse as the order's generator and a run narrower than one got nothing tried at all
     * (issue #903).
     *
     * <p>Which part of the region a level comes from settles itself: every part on the wrong side of
     * what has already been offered has its ends crossed and is passed over.
     */
    private static Offered drawnFrom(LevelSpace levels, LevelRegion region, Level from,
                                     Towards towards) {
        List<Level> out = new ArrayList<>();
        Bound past = from == null ? null : Bound.at(from, false);
        // <b>A level found and not offered, never a count that came out even.</b> A region holding
        // exactly this many and a region this stopped drawing from come back the same length, so
        // the figure being reached says nothing on its own — what says this compiler declined to
        // offer more is a level the region has that this did not take.
        boolean stoppedShort = false;
        while (true) {
            Level next = null;
            for (LevelInterval part : region.parts()) {
                LevelInterval left = towards == Towards.ABOVE
                        ? new LevelInterval(Bound.lower(past, part.low()), part.high())
                        : new LevelInterval(part.low(), Bound.upper(past, part.high()));
                if (left.crossed()) {
                    continue;
                }
                next = levels.witness(left, towards).level();
                if (next != null) {
                    break;
                }
            }
            if (next == null) {
                break;   // nothing further in the region, so this drew the whole of it
            }
            if (out.size() == LEVELS_TRIED) {
                stoppedShort = true;   // one the region has and this is not offering
                break;
            }
            out.add(next);
            past = Bound.at(next, false);
        }
        return new Offered(out, stoppedShort);
    }

    private LevelCandidateSource() {}
}
