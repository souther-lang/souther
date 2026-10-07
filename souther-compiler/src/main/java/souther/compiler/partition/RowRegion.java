package souther.compiler.partition;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which rows something is about, as the classes of the measured positions they may sit in.
 *
 * <p>Three answers and each is said as itself. Every row, no row, and the rows of some cells: a
 * condition this cannot place widens what is said towards the first, a way the model says no row
 * takes is the second, and the rest is the third. Held as collections whose emptiness meant one or
 * the other, what an absence said would be whichever reader was reading it.
 *
 * <p>The two operations a reader needs are here and nowhere else. Two conditions on one way hold
 * together ({@link #and}), and two ways to one place are either of them ({@link #or}) — so the rows
 * an obligation is about over several occurrences of it, or several readings, are the union, and a
 * row that escapes by any one of them is a row of the obligation.
 *
 * <p>Which direction a region is drawn in is its maker's to say. The rows an obligation asks for are
 * drawn wide, so that a row it asks for is in the region whatever the region could not read; the
 * rows a body answers nothing at are drawn narrow ({@link WhereNothingIsAnswered}). Asked whether
 * the first is inside the second, a yes is then a yes about the rows themselves.
 */
public sealed interface RowRegion {

    /** Every row. */
    RowRegion ALL = new All();

    /** No row. */
    RowRegion NONE = new None();

    /** Every row, whatever it holds. */
    record All() implements RowRegion {}

    /** No row at all. */
    record None() implements RowRegion {}

    /**
     * The rows in any one of these cells.
     *
     * @param cells never empty, and no cell of them leaves a position nothing
     */
    record Cells(List<Cell> cells) implements RowRegion {

        public Cells {
            cells = List.copyOf(new LinkedHashSet<>(cells));
            if (cells.isEmpty()) {
                throw new IllegalArgumentException("rows in no cell are no row");
            }
        }
    }

    /**
     * The rows that sit in one of the given classes at each position named.
     *
     * @param classes the classes each position is left, by the class's id. A position not named
     *                here may hold any class; one named is left at least one
     */
    record Cell(Map<AxisId, Set<String>> classes) {

        public Cell {
            Map<AxisId, Set<String>> copied = new HashMap<>();
            classes.forEach((axis, ids) -> {
                if (ids.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a cell leaves every position it names some class: " + axis);
                }
                copied.put(axis, Set.copyOf(ids));
            });
            classes = Collections.unmodifiableMap(copied);
        }

        /** The rows in both, or null where one position is left nothing by the two. */
        Cell and(Cell other) {
            Map<AxisId, Set<String>> both = new HashMap<>(classes);
            for (Map.Entry<AxisId, Set<String>> each : other.classes.entrySet()) {
                Set<String> here = both.get(each.getKey());
                if (here == null) {
                    both.put(each.getKey(), each.getValue());
                    continue;
                }
                Set<String> left = new HashSet<>(here);
                left.retainAll(each.getValue());
                if (left.isEmpty()) {
                    return null;
                }
                both.put(each.getKey(), left);
            }
            return new Cell(both);
        }

        /**
         * The classes {@code cell} leaves the positions of {@code axes} it narrows.
         *
         * <p>The one reading of a cell into classes, for both directions a region is drawn in: what
         * a cell admits at a position is what the classes are, whoever placed it.
         */
        static Cell of(InteractionCells.Cell cell, List<Axis> axes) {
            Map<AxisId, Set<String>> leaves = new HashMap<>();
            for (int axis = 0; axis < axes.size(); axis++) {
                if (!cell.narrows(axis)) {
                    continue;
                }
                Set<String> admitted = new HashSet<>();
                for (int c = 0; c < axes.get(axis).classes().size(); c++) {
                    if (cell.admits(axis, c)) {
                        admitted.add(axes.get(axis).classes().get(c).id());
                    }
                }
                leaves.put(axes.get(axis).id(), admitted);
            }
            return new Cell(leaves);
        }
    }

    /**
     * The rows in any of {@code cells}: none where there are none, and every row where one of them
     * names no position.
     */
    static RowRegion of(List<Cell> cells) {
        if (cells.isEmpty()) {
            return NONE;
        }
        for (Cell each : cells) {
            if (each.classes().isEmpty()) {
                return ALL;
            }
        }
        return new Cells(cells);
    }

    /** The rows in both. */
    default RowRegion and(RowRegion other) {
        return switch (this) {
            case None _ -> NONE;
            case All _ -> other;
            case Cells(var mine) -> switch (other) {
                case None _ -> NONE;
                case All _ -> this;
                case Cells(var theirs) -> {
                    List<Cell> both = new ArrayList<>();
                    for (Cell one : mine) {
                        for (Cell another : theirs) {
                            Cell met = one.and(another);
                            if (met != null) {
                                both.add(met);
                            }
                        }
                    }
                    yield of(both);
                }
            };
        };
    }

    /** The rows in either. */
    default RowRegion or(RowRegion other) {
        return switch (this) {
            case All _ -> ALL;
            case None _ -> other;
            case Cells(var mine) -> switch (other) {
                case All _ -> ALL;
                case None _ -> this;
                case Cells(var theirs) -> {
                    List<Cell> either = new ArrayList<>(mine);
                    either.addAll(theirs);
                    yield of(either);
                }
            };
        };
    }
}
