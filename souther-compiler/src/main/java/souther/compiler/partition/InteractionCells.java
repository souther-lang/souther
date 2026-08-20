package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.interaction.Condition;
import souther.compiler.interaction.Factor;
import souther.compiler.interaction.Interaction;
import souther.compiler.interaction.Outcome;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * The combinations a group of decisions has, as the classes a row filling one sits in.
 *
 * <p>Two vocabularies meeting. A decision is read off the body and says which way a comparison came
 * out or which case a union was matched at; a row is written at classes of the input positions. The
 * two are about the same rules — the comparison a factor names is the comparison a cut was drawn
 * off — so this is a lookup rather than a second derivation of where the model divides.
 *
 * <p>A group is offered only where every condition it is made of places at a class. What a cell is
 * for is a row that takes the path to the meeting and settles each factor at the outcome the cell
 * names, and a condition with no class to put a row at leaves both open: the row may go the other
 * way round the fork above, or take a different outcome of the factor, and either way it is offered
 * for a combination it does not sit in. A row already written reads the same way — the cell would
 * be taken for covered by a row that never reaches the operator. So the group goes, and what is
 * left is the pair space, which is where such a behavior already was.
 *
 * <p>A factor whose outcomes place at the same classes goes for the second half of the same reason:
 * no row can be steered from one to the other, so the cells over it are one row asked for several
 * times.
 */
public final class InteractionCells {

    /**
     * How many combinations a group may have and still be offered.
     *
     * <p>A group is taken from while there is budget for a row and no further, so what this bounds
     * is not how many rows come out of it. It bounds the walk over its combinations, which goes on
     * past the ones already answered and the ones nothing could be built for — and a group whose
     * product runs to the billions would have that walk stand between the author and every other
     * group. Wide enough that a group the budget could work through is never cut, and the number is
     * the group's own and known before any of it is built.
     */
    private static final int MOST_CELLS = 4096;

    private InteractionCells() {}

    /**
     * One group's combinations, as somewhere to read them from rather than as a list.
     *
     * <p>Nothing is built until it is asked for. Which combinations get offered is the row budget's
     * to decide, and a list built beforehand would have to guess how much of it the budget reaches:
     * a combination a written row already sits in costs no row, so a caller that stopped enumerating
     * at the budget would leave the ones past that point untried while the budget still held.
     *
     * @param reach     the classes the path to the meeting puts a row at, which every combination
     *                  is under
     * @param byFactor  where each outcome of each factor puts a row, one list per factor
     * @param positions how many positions a cell is over
     */
    public record Group(int[] reach, List<List<int[]>> byFactor, int positions) {

        public Group {
            reach = reach.clone();
            byFactor = List.copyOf(byFactor);
        }

        /**
         * How many ways there are to choose one outcome from each factor.
         *
         * <p>Not how many combinations the group has: two factors reading one position have choices
         * that put it at two classes, and no row is written at those. This is the space the choices
         * are counted off, and {@link #at} says which of them are cells.
         */
        public int size() {
            long size = 1;
            for (List<int[]> factor : byFactor) {
                size *= factor.size();
                if (size >= MOST_CELLS) {
                    return MOST_CELLS;
                }
            }
            return (int) size;
        }

        /**
         * The {@code index}th choice as a cell, or null where the factors it takes disagree.
         *
         * <p>Disagreeing is not a combination the body refuses. There is no path through the body
         * that takes both, so there is nothing there to ask for.
         */
        public int[] at(int index) {
            int[] at = reach.clone();
            int left = index;
            for (List<int[]> factor : byFactor) {
                int[] outcome = factor.get(left % factor.size());
                left /= factor.size();
                for (int i = 0; i < at.length; i++) {
                    if (outcome[i] < 0) {
                        continue;
                    }
                    if (at[i] >= 0 && at[i] != outcome[i]) {
                        return null;
                    }
                    at[i] = outcome[i];
                }
            }
            return at;
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
            int[] reach = placedBy(group.reach(), axes);
            if (reach == null) {
                continue;
            }
            List<List<int[]>> placed = factorsOf(group, axes);
            if (placed == null || productOf(placed) >= MOST_CELLS) {
                continue;
            }
            Group built = new Group(reach, placed, axes.size());
            if (built.left(0) > 0) {
                out.add(built);
            }
        }
        return List.copyOf(out);
    }

    /** How far the product runs, stopping where it is past anything that would be offered. */
    private static long productOf(List<List<int[]>> placed) {
        long size = 1;
        for (List<int[]> factor : placed) {
            size *= factor.size();
            if (size >= MOST_CELLS) {
                return MOST_CELLS;
            }
        }
        return size;
    }

    /** Where each outcome of each factor puts a row, or null where the group is not one to offer. */
    private static List<List<int[]>> factorsOf(Interaction group, List<Axis> axes) {
        List<List<int[]>> out = new ArrayList<>();
        for (Factor factor : group.factors()) {
            List<int[]> placements = new ArrayList<>();
            for (Outcome outcome : factor.outcomes()) {
                int[] at = placedBy(outcome.holds(), axes);
                if (at == null || alreadyThere(placements, at)) {
                    return null;
                }
                placements.add(at);
            }
            out.add(placements);
        }
        return out;
    }

    /** Where {@code holds} puts a row, or null where any of it places at no class. */
    private static int[] placedBy(List<Condition> holds, List<Axis> axes) {
        int[] at = new int[axes.size()];
        Arrays.fill(at, -1);
        for (Condition each : holds) {
            if (!place(each, axes, at)) {
                return null;
            }
        }
        return at;
    }

    private static boolean alreadyThere(List<int[]> placements, int[] at) {
        for (int[] each : placements) {
            if (Arrays.equals(each, at)) {
                return true;
            }
        }
        return false;
    }

    /** The class {@code condition} settles its position at, where this can say which. */
    private static boolean place(Condition condition, List<Axis> axes, int[] at) {
        switch (condition) {
            case Condition.Case one -> {
                int axis = axisAt(axes, one.at());
                if (axis < 0) {
                    return false;
                }
                List<PartitionClass> classes = axes.get(axis).classes();
                for (int c = 0; c < classes.size(); c++) {
                    if (classes.get(c).label().equals(one.name())) {
                        at[axis] = c;
                        return true;
                    }
                }
                return false;
            }
            case Condition.Side one -> {
                int axis = axisAt(axes, one.at());
                if (axis < 0) {
                    return false;
                }
                Cut line = cutAt(axes.get(axis), one.site());
                if (line == null) {
                    return false;
                }
                OriginRef.GuardOrigin guard = guardOf(line, one.site());
                int home = holding(axes.get(axis), line);
                if (home < 0) {
                    return false;
                }
                // Which side the comparison is true on, from the two facts the line carries: which
                // side of it the cut value itself sits on, and whether the comparison holds there.
                boolean homeSideIsUp = !guard.valueBelongsBelow();
                boolean wantedIsHomeSide = guard.holdsAtTheValue() == one.held();
                boolean wantedIsUp = wantedIsHomeSide == homeSideIsUp;
                int nearest = wantedIsHomeSide ? home : (wantedIsUp ? home + 1 : home - 1);
                if (nearest < 0 || nearest >= axes.get(axis).classes().size()) {
                    return false;
                }
                at[axis] = nearest;
                return true;
            }
            // A fork this reading could not name a position for puts a row nowhere.
            case Condition.Arm ignored -> {
                return false;
            }
        }
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
    private static Cut cutAt(Axis axis, int site) {
        for (Cut each : axis.cuts()) {
            if (guardOf(each, site) != null) {
                return each;
            }
        }
        return null;
    }

    /** Which rule of the cut this reading of the comparison is. */
    private static OriginRef.GuardOrigin guardOf(Cut cut, int site) {
        for (OriginRef origin : cut.origins()) {
            if (origin instanceof OriginRef.GuardOrigin guard && guard.read().site() == site) {
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
