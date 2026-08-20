package souther.compiler.partition;

import souther.compiler.interaction.Condition;
import souther.compiler.interaction.Factor;
import souther.compiler.interaction.Interaction;
import souther.compiler.interaction.Outcome;

import java.util.ArrayList;
import java.util.List;

/**
 * The combinations a group of decisions has, as the classes a row filling one sits in.
 *
 * <p>Two vocabularies meeting. A decision is read off the body and says which way a comparison came
 * out or which case a union was matched at; a row is written at classes of the input positions. The
 * two are about the same rules — the comparison a factor names is the comparison a cut was drawn
 * off — so this is a lookup rather than a second derivation of where the model divides.
 *
 * <p>A condition this cannot place leaves its position free rather than taking the cell away. A cell
 * that fixes fewer positions is a weaker request and still a real one; a cell dropped is a
 * combination nobody is asked for.
 */
public final class InteractionCells {

    private InteractionCells() {}

    /** One cell per combination of the group's factors, over the ordered {@code axes}. */
    public static List<Generator.Cell> of(List<Interaction> groups, List<Axis> axes) {
        List<Generator.Cell> cells = new ArrayList<>();
        for (Interaction group : groups) {
            for (List<Condition> holds : combinations(group.factors())) {
                int[] at = new int[axes.size()];
                java.util.Arrays.fill(at, -1);
                for (Condition each : holds) {
                    place(each, axes, at);
                }
                cells.add(new Generator.Cell(at));
            }
        }
        return List.copyOf(cells);
    }

    /** Every way one outcome of each factor can be taken together. */
    private static List<List<Condition>> combinations(List<Factor> factors) {
        List<List<Condition>> out = new ArrayList<>();
        out.add(List.of());
        for (Factor factor : factors) {
            List<List<Condition>> next = new ArrayList<>();
            for (List<Condition> so_far : out) {
                for (Outcome outcome : factor.outcomes()) {
                    List<Condition> both = new ArrayList<>(so_far);
                    both.addAll(outcome.holds());
                    next.add(both);
                }
            }
            out = next;
        }
        return out;
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
            // A fork this reading could not name a position for steers nothing. The outcomes are
            // still two, so the cells are still two; what they do not carry is where to put a row.
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
    private static int axisAt(List<Axis> axes, souther.compiler.inputs.TermPath path) {
        int found = -1;
        int deepest = -1;
        for (int i = 0; i < axes.size(); i++) {
            souther.compiler.inputs.TermPath at = axes.get(i).path();
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
