package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.interaction.Condition;
import souther.compiler.interaction.Factor;
import souther.compiler.interaction.Interaction;
import souther.compiler.interaction.Outcome;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The combinations a group of decisions has, as the classes a row filling one sits in.
 *
 * <p>Two vocabularies meeting. A decision is read off the body and says which way a comparison came
 * out or which case a union was matched at; a row is written at classes of the input positions. The
 * two are about the same rules — the comparison a factor names is the comparison a cut was drawn
 * off — so this is a lookup rather than a second derivation of where the model divides.
 *
 * <p>A group whose factors cannot each be told apart in that vocabulary is not offered at all. A
 * factor whose outcomes place at the same classes is one no row can be steered around, so the cells
 * over it are the same row asked for several times; and one that places at nothing is a decision
 * this reading knows is there and cannot reach. Offering either would hand an author rows that
 * establish nothing, which is the defect the group was read to avoid — so the group goes, and what
 * is left is the pair space, which is where such a behavior already was.
 *
 * <p>Nor is a group offered where two of its factors read one position. A row cannot put that
 * position at two classes, so the combinations of the two are not the product of them and there is
 * no count of the group that is not itself an enumeration. What such a group would ask about the
 * shared position is what covering that position's classes asks already.
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
     * @param byFactor  where each outcome of each factor puts a row, one list per factor
     * @param positions how many positions a cell is over
     */
    public record Group(List<List<int[]>> byFactor, int positions) {

        public Group {
            byFactor = List.copyOf(byFactor);
        }

        /**
         * How many combinations the group has.
         *
         * <p>Exact, and known without building any of them: the factors read no position in common,
         * so every choice of one outcome from each is a cell.
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

        /** The {@code index}th combination, counting the factors off in the order they are read. */
        public int[] at(int index) {
            int[] at = new int[positions];
            Arrays.fill(at, -1);
            int left = index;
            for (List<int[]> factor : byFactor) {
                int[] outcome = factor.get(left % factor.size());
                left /= factor.size();
                for (int i = 0; i < at.length; i++) {
                    if (outcome[i] >= 0) {
                        at[i] = outcome[i];
                    }
                }
            }
            return at;
        }
    }

    /** The groups worth offering, over the ordered {@code axes}. */
    public static List<Group> of(List<Interaction> groups, List<Axis> axes) {
        List<Group> out = new ArrayList<>();
        for (Interaction group : groups) {
            List<List<int[]>> placed = placedBy(group, axes);
            if (placed != null && productOf(placed) < MOST_CELLS) {
                out.add(new Group(placed, axes.size()));
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

    /**
     * Where each outcome of each factor puts a row, or null where the group is not one to offer.
     */
    private static List<List<int[]>> placedBy(Interaction group, List<Axis> axes) {
        List<List<int[]>> out = new ArrayList<>();
        Set<Integer> taken = new LinkedHashSet<>();
        for (Factor factor : group.factors()) {
            List<int[]> placements = new ArrayList<>();
            Set<Integer> reads = new LinkedHashSet<>();
            for (Outcome outcome : factor.outcomes()) {
                int[] at = new int[axes.size()];
                Arrays.fill(at, -1);
                for (Condition each : outcome.holds()) {
                    place(each, axes, at);
                }
                if (fixesNothing(at) || alreadyThere(placements, at)) {
                    return null;
                }
                for (int i = 0; i < at.length; i++) {
                    if (at[i] >= 0) {
                        reads.add(i);
                    }
                }
                placements.add(at);
            }
            for (int position : reads) {
                if (!taken.add(position)) {
                    return null;
                }
            }
            out.add(placements);
        }
        return out;
    }

    private static boolean fixesNothing(int[] at) {
        for (int each : at) {
            if (each >= 0) {
                return false;
            }
        }
        return true;
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
    private static void place(Condition condition, List<Axis> axes, int[] at) {
        switch (condition) {
            case Condition.Case one -> {
                int axis = axisAt(axes, one.at());
                if (axis < 0) {
                    return;
                }
                List<PartitionClass> classes = axes.get(axis).classes();
                for (int c = 0; c < classes.size(); c++) {
                    if (classes.get(c).label().equals(one.name())) {
                        at[axis] = c;
                        return;
                    }
                }
            }
            case Condition.Side one -> {
                int axis = axisAt(axes, one.at());
                if (axis < 0) {
                    return;
                }
                Cut line = cutAt(axes.get(axis), one.site());
                if (line == null) {
                    return;
                }
                OriginRef.GuardOrigin guard = guardOf(line, one.site());
                int home = holding(axes.get(axis), line);
                if (home < 0) {
                    return;
                }
                // Which side the comparison is true on, from the two facts the line carries: which
                // side of it the cut value itself sits on, and whether the comparison holds there.
                boolean homeSideIsUp = !guard.valueBelongsBelow();
                boolean wantedIsHomeSide = guard.holdsAtTheValue() == one.held();
                boolean wantedIsUp = wantedIsHomeSide == homeSideIsUp;
                int nearest = wantedIsHomeSide ? home : (wantedIsUp ? home + 1 : home - 1);
                if (nearest >= 0 && nearest < axes.get(axis).classes().size()) {
                    at[axis] = nearest;
                }
            }
            // A fork this reading could not name a position for steers nothing. The group it is a
            // factor of goes, because a factor nothing can steer is one no row varies.
            case Condition.Arm ignored -> { }
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
