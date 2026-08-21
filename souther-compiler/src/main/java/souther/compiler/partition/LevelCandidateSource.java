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
    private static final int LEVELS_TRIED = 8;

    /**
     * The levels a row at this item could stand at, nearest the line first.
     *
     * <p>A point stands at one level and nowhere else — a level further out is a different point of
     * the border, and offering it would answer a question nobody asked. A run is met anywhere in it,
     * and a class of everything but one value at either of the two sides of it, so both are asked
     * for outward from what they are written against until the budget runs out. Which is why a run
     * that came back empty settles nothing while a point may.
     */
    public static List<Level> forItem(Criterion where, LevelSpace levels) {
        Level from = where.anchor();
        return switch (where) {
            case Criterion.AtTheLevel _ -> List.of(from);
            case Criterion.Within within -> inside(levels, within);
            case Criterion.AnythingBut other -> {
                // Above first and then below, which is a choice and not a reading of the two sides:
                // a value is singled out of an order that runs both ways and neither side is the
                // nearer. Said in one place so that a report's rows do not turn on where a reader
                // happened to start.
                List<Level> either = new ArrayList<>(
                        drawnFrom(levels, other.region(), from, Towards.ABOVE));
                either.addAll(drawnFrom(levels, other.region(), from, Towards.BELOW));
                yield either;
            }
        };
    }

    /**
     * The levels of a run a row could stand at, from the line inward.
     *
     * <p>The value against the line is the one level of the run that will not do, so the search
     * starts there and walks away from it, which is the direction the point is named for. Walked
     * from the run's far end instead, a row well inside a wide run was offered where one just inside
     * it says the same thing and is the row an author would have written.
     */
    private static List<Level> inside(LevelSpace levels, Criterion.Within within) {
        Level from = within.anchor();
        if (from == null) {
            return List.of();
        }
        List<Level> out = new ArrayList<>();
        if (within.holds(from)) {
            out.add(from);
        }
        out.addAll(drawnFrom(levels, within.region(), from, away(within)));
        return out;
    }

    /**
     * Which end of this run a row is wanted nearest, which is the end the line is at.
     *
     * <p>The one place that says it, read by everything that composes a row inside a run — the
     * search that picks a level of a form and the one that picks a place of a carrier alike. Said
     * separately, each of them was near the line for its own reason and only one of them on purpose.
     */
    public static Towards nearestEndOf(Criterion.Within within) {
        return away(within);
    }

    /** Which way from the line this run lies, which is which end of it the line is at. */
    private static Towards away(Criterion.Within within) {
        Band band = within.band();
        Level except = within.except();
        if (except != null && band.first() != null
                && except.key().equals(band.first().key())) {
            return Towards.ABOVE;
        }
        if (except != null && band.last() != null && except.key().equals(band.last().key())) {
            return Towards.BELOW;
        }
        return band.under() != null ? Towards.ABOVE : Towards.BELOW;
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
    private static List<Level> drawnFrom(LevelSpace levels, LevelRegion region, Level from,
                                         Towards towards) {
        List<Level> out = new ArrayList<>();
        Bound past = from == null ? null : Bound.at(from, false);
        for (int step = 0; step < LEVELS_TRIED; step++) {
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
                break;
            }
            out.add(next);
            past = Bound.at(next, false);
        }
        return out;
    }

    private LevelCandidateSource() {}
}
