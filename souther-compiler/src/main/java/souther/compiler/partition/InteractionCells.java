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
 * <p>A group whose factors cannot each be told apart in that vocabulary is not offered at all. A
 * factor whose outcomes place at the same classes is one no row can be steered around, so the cells
 * over it are the same row asked for several times; and one that places at nothing is a decision
 * this reading knows is there and cannot reach. Offering either would hand an author rows that
 * establish nothing, which is the defect the group was read to avoid — so the group goes, and what
 * is left is the pair space, which is where such a behavior already was.
 */
public final class InteractionCells {

    private InteractionCells() {}

    /**
     * One group's combinations, and how many of them there are.
     *
     * <p>The two are not the same number where the enumeration was cut short, which is why the size
     * is carried rather than read off the list. A caller saying how much of a group it did not get
     * to has to say it about the group and not about the part of it that was built.
     *
     * @param size  how many combinations the group has. What was enumerated where that finished,
     *              and the product of the factors — an upper bound, since two factors reading one
     *              position have combinations they disagree at — where it did not
     * @param cells the ones that were built, in the order the factors are taken
     */
    public record Group(int size, List<Generator.Cell> cells) {

        public Group {
            cells = List.copyOf(cells);
        }
    }

    /**
     * The cells of each group over the ordered {@code axes}.
     *
     * <p>Kept per group rather than run together so a caller with a row budget can spend it across
     * the groups instead of on whichever the walk met first.
     *
     * @param most how many cells of one group are worth building. Beyond what a caller can offer,
     *             enumerating is work whose answer is thrown away
     */
    public static List<Group> of(List<Interaction> groups, List<Axis> axes, int most) {
        List<Group> out = new ArrayList<>();
        for (Interaction group : groups) {
            List<List<int[]>> placed = placedBy(group, axes);
            if (placed == null) {
                continue;
            }
            Group built = cellsOf(placed, axes.size(), most);
            if (!built.cells().isEmpty()) {
                out.add(built);
            }
        }
        return List.copyOf(out);
    }

    /** How many combinations the factors have between them, as far as an {@code int} says it. */
    private static int productOf(List<List<int[]>> placed) {
        long size = 1;
        for (List<int[]> factor : placed) {
            size *= factor.size();
            if (size >= Integer.MAX_VALUE) {
                return Integer.MAX_VALUE;
            }
        }
        return (int) size;
    }

    /**
     * Where each outcome of each factor puts a row, or null where a factor cannot be told apart.
     */
    private static List<List<int[]>> placedBy(Interaction group, List<Axis> axes) {
        List<List<int[]>> out = new ArrayList<>();
        for (Factor factor : group.factors()) {
            List<int[]> placements = new ArrayList<>();
            for (Outcome outcome : factor.outcomes()) {
                int[] at = new int[axes.size()];
                Arrays.fill(at, -1);
                for (Condition each : outcome.holds()) {
                    place(each, axes, at);
                }
                if (fixesNothing(at) || alreadyThere(placements, at)) {
                    return null;
                }
                placements.add(at);
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

    /** Every way one outcome of each factor can be taken together, where they agree. */
    private static Group cellsOf(List<List<int[]>> placed, int positions, int most) {
        boolean cut = false;
        List<int[]> out = new ArrayList<>();
        int[] nothing = new int[positions];
        Arrays.fill(nothing, -1);
        out.add(nothing);
        for (List<int[]> factor : placed) {
            List<int[]> next = new ArrayList<>();
            // Per factor, because it says this factor's expansion stopped. Kept across them only as
            // the answer to whether anything was left out at all.
            boolean full = false;
            for (int[] soFar : out) {
                for (int[] outcome : factor) {
                    int[] both = merged(soFar, outcome);
                    // Two factors reading one position leave the combinations they disagree at
                    // unbuilt. Such a combination is not one the body refuses; there is no path
                    // through the body that takes both, so there is nothing there to ask for.
                    if (both != null) {
                        next.add(both);
                    }
                    if (next.size() >= most) {
                        cut = true;
                        full = true;
                        break;
                    }
                }
                if (full) {
                    break;
                }
            }
            out = next;
        }
        return new Group(cut ? productOf(placed) : out.size(),
                out.stream().map(Generator.Cell::new).toList());
    }

    /** The two together, or null where they fix one position at two classes. */
    private static int[] merged(int[] one, int[] other) {
        int[] both = one.clone();
        for (int i = 0; i < both.length; i++) {
            if (other[i] < 0) {
                continue;
            }
            if (both[i] >= 0 && both[i] != other[i]) {
                return null;
            }
            both[i] = other[i];
        }
        return both;
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
