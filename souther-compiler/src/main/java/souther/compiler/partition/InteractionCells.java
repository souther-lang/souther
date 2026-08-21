package souther.compiler.partition;

import souther.compiler.coverage.ComparisonOccurrence;
import souther.compiler.inputs.TermPath;
import souther.compiler.interaction.Condition;
import souther.compiler.interaction.Factor;
import souther.compiler.interaction.Interaction;
import souther.compiler.interaction.Outcome;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The combinations a group of decisions has, as the classes a row filling one may sit in.
 *
 * <p>Two vocabularies meeting. A decision is read off the body and says which way a comparison came
 * out or which case a union was matched at; a row is written at classes of the input positions. The
 * two are about the same rules — the comparison a factor names is the comparison a cut was drawn
 * off — so this is a lookup rather than a second derivation of where the model divides.
 *
 * <p>A condition is a constraint and not a choice of class. {@code n > 10} leaves every class above
 * the line, and picking one of them here would answer for the condition alone and be wrong as soon
 * as a second one arrives: under {@code if n > 10 { if n > 0 { … } }} the way in is both, and a
 * reading that wrote a class down for each would keep the last. So a cell carries which classes each
 * position may hold, one condition narrows it, and a cell nothing is left at is not a combination.
 *
 * <p>A group is offered only where every condition it is made of narrows something. What a cell is
 * for is a row that takes the path to the meeting and settles each factor at the outcome the cell
 * names, and a condition with no classes to put a row at leaves both open: the row may go the other
 * way round the fork above, or take a different outcome of the factor, and either way it is offered
 * for a combination it does not sit in. A row already written reads the same way — the cell would be
 * taken for covered by a row that never reaches the operator. So the group goes, and what is left is
 * the pair space, which is where such a behavior already was.
 *
 * <p>A factor whose outcomes leave the same classes goes for the second half of the same reason: no
 * row can be steered from one to the other, so the cells over it are one row asked for several times.
 */
public final class InteractionCells {

    /**
     * How many ways of choosing an outcome from each factor a group may have and still be offered.
     *
     * <p>A group is taken from while there is budget for a row and no further, so what this bounds
     * is not how many rows come out of it. It bounds the walk over its choices, which goes on past
     * the ones already answered, the ones the factors disagree about and the ones nothing could be
     * built for — and a group whose choices run to the billions would have that walk stand between
     * the author and every other group. The number is the group's own and known before any of it is
     * built.
     */
    private static final int MOST_CELLS = 4096;

    private InteractionCells() {}

    /**
     * Which classes of each position a row may sit in, as far as something has said.
     *
     * @param allowed one flag per class of each position, in the order the axes are ordered
     */
    public record Cell(boolean[][] allowed) {

        /** Nothing said yet: every class of every position is still open. */
        public static Cell anything(List<Axis> axes) {
            boolean[][] allowed = new boolean[axes.size()][];
            for (int i = 0; i < axes.size(); i++) {
                allowed[i] = new boolean[axes.get(i).classes().size()];
                Arrays.fill(allowed[i], true);
            }
            return new Cell(allowed);
        }

        /** Both, or null where they leave a position nothing. */
        public Cell and(Cell other) {
            boolean[][] both = new boolean[allowed.length][];
            for (int i = 0; i < allowed.length; i++) {
                both[i] = allowed[i].clone();
                boolean any = false;
                for (int c = 0; c < both[i].length; c++) {
                    both[i][c] &= other.allowed[i][c];
                    any |= both[i][c];
                }
                if (!any && both[i].length > 0) {
                    return null;
                }
            }
            return new Cell(both);
        }

        /** Whether this says anything about the position, which is what a row is named for. */
        public boolean narrows(int axis) {
            for (boolean each : allowed[axis]) {
                if (!each) {
                    return true;
                }
            }
            return false;
        }

        public boolean admits(int axis, int cls) {
            return cls >= 0 && cls < allowed[axis].length && allowed[axis][cls];
        }

        public boolean sameAs(Cell other) {
            return Arrays.deepEquals(allowed, other.allowed);
        }
    }

    /**
     * One group's combinations, as somewhere to read them from rather than as a list.
     *
     * <p>Nothing is built until it is asked for. Which combinations get offered is the row budget's
     * to decide, and a list built beforehand would have to guess how much of it the budget reaches:
     * a combination a written row already sits in costs no row, so a caller that stopped enumerating
     * at the budget would leave the ones past that point untried while the budget still held.
     *
     * @param reach    what the path to the meeting leaves open, which every combination is under
     * @param byFactor what each outcome of each factor leaves open, one list per factor
     */
    public record Group(Cell reach, List<List<Cell>> byFactor) {

        public Group {
            byFactor = List.copyOf(byFactor);
        }

        /**
         * How many ways there are to choose one outcome from each factor.
         *
         * <p>Not how many combinations the group has: two factors reading one position have choices
         * that leave it nothing, and no row is written at those. This is the space the choices are
         * counted off, and {@link #at} says which of them are cells.
         */
        public int size() {
            long size = 1;
            for (List<Cell> factor : byFactor) {
                size *= factor.size();
                if (size >= MOST_CELLS) {
                    return MOST_CELLS;
                }
            }
            return (int) size;
        }

        /**
         * The {@code index}th choice as a cell, or null where the factors it takes leave a position
         * nothing.
         *
         * <p>Leaving a position nothing is not a combination the body refuses. There is no path
         * through the body that takes both, so there is nothing there to ask for.
         */
        public Cell at(int index) {
            Cell cell = reach;
            int left = index;
            for (List<Cell> factor : byFactor) {
                cell = cell.and(factor.get(left % factor.size()));
                if (cell == null) {
                    return null;
                }
                left /= factor.size();
            }
            return cell;
        }

        /** How many cells the group has from {@code from} on, which is what a stopped search left. */
        public int left(int from) {
            int left = 0;
            for (int index = from; index < size(); index++) {
                if (at(index) != null) {
                    left++;
                }
            }
            return left;
        }
    }

    /** The groups worth offering, over the ordered {@code axes}. */
    public static List<Group> of(List<Interaction> groups, List<Axis> axes) {
        List<Group> out = new ArrayList<>();
        for (Interaction group : groups) {
            Cell reach = narrowedBy(group.reach(), axes);
            if (reach == null) {
                continue;
            }
            List<List<Cell>> placed = factorsOf(group, axes);
            if (placed == null || productOf(placed) >= MOST_CELLS) {
                continue;
            }
            Group built = new Group(reach, placed);
            if (built.left(0) > 0) {
                out.add(built);
            }
        }
        return List.copyOf(out);
    }

    /** How far the product runs, stopping where it is past anything that would be offered. */
    private static long productOf(List<List<Cell>> placed) {
        long size = 1;
        for (List<Cell> factor : placed) {
            size *= factor.size();
            if (size >= MOST_CELLS) {
                return MOST_CELLS;
            }
        }
        return size;
    }

    /** What each outcome of each factor leaves open, or null where the group is not one to offer. */
    private static List<List<Cell>> factorsOf(Interaction group, List<Axis> axes) {
        List<List<Cell>> out = new ArrayList<>();
        for (Factor factor : group.factors()) {
            List<Cell> outcomes = new ArrayList<>();
            for (Outcome outcome : factor.outcomes()) {
                Cell at = narrowedBy(outcome.holds(), axes);
                if (at == null || alreadyThere(outcomes, at)) {
                    return null;
                }
                outcomes.add(at);
            }
            out.add(outcomes);
        }
        return out;
    }

    /** What {@code holds} leaves open, or null where any of it narrows nothing or narrows it away. */
    private static Cell narrowedBy(List<Condition> holds, List<Axis> axes) {
        Cell cell = Cell.anything(axes);
        for (Condition each : holds) {
            Cell said = admittedBy(each, axes);
            if (said == null) {
                return null;
            }
            cell = cell.and(said);
            if (cell == null) {
                return null;
            }
        }
        return cell;
    }

    private static boolean alreadyThere(List<Cell> outcomes, Cell at) {
        for (Cell each : outcomes) {
            if (each.sameAs(at)) {
                return true;
            }
        }
        return false;
    }

    /** Which classes {@code condition} leaves its position, or null where it names none. */
    private static Cell admittedBy(Condition condition, List<Axis> axes) {
        switch (condition) {
            case Condition.Case one -> {
                int axis = axisAt(axes, one.at());
                if (axis < 0) {
                    return null;
                }
                List<PartitionClass> classes = axes.get(axis).classes();
                for (int c = 0; c < classes.size(); c++) {
                    if (classes.get(c).label().equals(one.name())) {
                        return only(axes, axis, c, c);
                    }
                }
                return null;
            }
            case Condition.Side one -> {
                int axis = axisAt(axes, one.at());
                if (axis < 0) {
                    return null;
                }
                Cut line = cutAt(axes.get(axis), one.comparison());
                if (line == null) {
                    return null;
                }
                OriginRef.GuardOrigin guard = guardOf(line, one.comparison());
                int home = holding(axes.get(axis), line);
                if (home < 0) {
                    return null;
                }
                // Which side the comparison is true on, from the two facts the line carries: which
                // side of it the cut value itself sits on, and whether the comparison holds there.
                // The whole side and not its nearest class: the comparison admits every value out
                // that way, and a reading that answered with one of them would have said more than
                // the rule does — which is what makes two of them impossible to take together.
                boolean homeSideIsUp = !guard.valueBelongsBelow();
                boolean wantedIsHomeSide = guard.holdsAtTheValue() == one.held();
                boolean wantedIsUp = wantedIsHomeSide == homeSideIsUp;
                int last = axes.get(axis).classes().size() - 1;
                int edge = wantedIsHomeSide ? home : (wantedIsUp ? home + 1 : home - 1);
                if (edge < 0 || edge > last) {
                    return null;
                }
                return wantedIsUp ? only(axes, axis, edge, last) : only(axes, axis, 0, edge);
            }
            // A fork this reading could not name a position for narrows nothing.
            case Condition.Arm ignored -> {
                return null;
            }
        }
    }

    /** Everything open but {@code axis}, which is left the classes from {@code from} to {@code to}. */
    private static Cell only(List<Axis> axes, int axis, int from, int to) {
        Cell cell = Cell.anything(axes);
        Arrays.fill(cell.allowed()[axis], false);
        for (int c = from; c <= to; c++) {
            cell.allowed()[axis][c] = true;
        }
        return cell;
    }

    /**
     * Which position the condition is about, allowing for the names a value is written under.
     *
     * <p>{@code total.value} and {@code total} are one position where {@code Total} is a name worn
     * over an {@code Int}: the body reads through the name and the partition divides the position
     * the name is at. The longest match wins, so a record whose own field is divided keeps its own
     * axis rather than being answered by the record's.
     */
    private static int axisAt(List<Axis> axes, TermPath path) {
        int found = -1;
        int deepest = -1;
        for (int i = 0; i < axes.size(); i++) {
            TermPath at = axes.get(i).path();
            if (!at.head().equals(path.head()) || at.fields().size() > path.fields().size()) {
                continue;
            }
            if (path.fields().subList(0, at.fields().size()).equals(at.fields())
                    && at.fields().size() > deepest) {
                deepest = at.fields().size();
                found = i;
            }
        }
        return found;
    }

    /** The cut this reading of the comparison drew, or null where it drew none. */
    private static Cut cutAt(Axis axis, ComparisonOccurrence comparison) {
        for (Cut each : axis.cuts()) {
            if (guardOf(each, comparison) != null) {
                return each;
            }
        }
        return null;
    }

    /** Which rule of the cut this reading of the comparison is. */
    private static OriginRef.GuardOrigin guardOf(Cut cut, ComparisonOccurrence comparison) {
        for (OriginRef origin : cut.origins()) {
            if (origin instanceof OriginRef.GuardOrigin guard
                    && guard.read().comparison().equals(comparison)) {
                return guard;
            }
        }
        return null;
    }

    /** Which class of the axis holds the value the line is drawn at. */
    private static int holding(Axis axis, Cut line) {
        List<PartitionClass> classes = axis.classes();
        for (int c = 0; c < classes.size(); c++) {
            if (classes.get(c).classifier().membershipOf(line.value())
                    instanceof souther.compiler.inputs.Membership.Match) {
                return c;
            }
        }
        return -1;
    }
}
