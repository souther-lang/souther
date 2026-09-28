package souther.compiler.query;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.partition.QuantityKey;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The lines a border is held against: the ones it would have been had a position been weighed
 * differently.
 *
 * <p>What a coverage measure counts is rows, and what it is <em>for</em> is faults a row would show.
 * The four points of a border are asked for because a row at each of them shows a line that has
 * moved, which is a wrong constant; a line that has turned is a wrong coefficient, and no number of
 * rows at one place shows one (White &amp; Cohen, "A Domain Strategy for Computer Program Testing",
 * IEEE TSE SE-6(3), 1980). So which lines a border is <em>not</em> is asked here, and a row that
 * answers differently at one of them is what tells the two apart.
 *
 * <p><b>A family the model derives and a build does not choose.</b> One position weighed one more or
 * one less, and nothing else. A family a caller could widen would be a dial on what a build refuses
 * over, and a wider one would leave every model short of an adequacy nothing reaches.
 *
 * <p><b>So what turning every one of them away establishes is that, and not that the line has not
 * turned.</b> These are the lines one step away, and a line two steps away is not among them: over
 * positions whose values fill, {@code 2.5} lies between the weights this enumerates and rows that
 * turn away the weights either side of it need not turn it away. What a border that survives them
 * has been shown is that no fault of one step in one weight is left — which is a fault domain
 * stated, the way a fault domain always is, and never the geometry of the line pinned down. A line
 * held against every line there is takes constraints at several places along it rather than a
 * neighbourhood around it (White &amp; Cohen's N&#215;1), and that is a different measure from this
 * one.
 *
 * <p>In the quantity's own weights and not the ones a rule happened to write. {@code 300 * straw +
 * 600 * choco} weighs one of them twice the other, and a line one step from it is one weighing them
 * one and three — asked of the written numbers, the step would be a three-hundredth of a turn and
 * every model would pass.
 *
 * <p>A quantity over one position has no family at all. Weighed one less it is nothing, and weighed
 * one more it is the same line — which is what it means for a bound on a position to have no turn in
 * it, and why the four points are the whole of what such a border is owed.
 *
 * <p><b>And a position is weighed only where a model could write the weight.</b> A date counts from
 * an origin nobody wrote, so twice a date is a number and no date, and a line weighing one of them
 * two is a line nobody can state ({@link souther.compiler.check.Carrier#canBeWeighed}). A rule
 * holding two dates apart weighs them one and minus one, where the origins cancel, and that is the
 * one pair of weights it has — so such a border can shift and cannot turn, and it is owed nothing
 * here either.
 *
 * @param wrote   the direction the model's rule runs in
 * @param weighed the positions of it a rule could write another weight for
 */
public record FaultFamily(QuantityKey wrote, Set<NumericTerm> weighed) {

    public FaultFamily {
        if (wrote == null || wrote.direction().isEmpty()) {
            throw new IllegalArgumentException("a family is the lines beside a line: " + wrote);
        }
        if (!wrote.direction().keySet().containsAll(weighed)) {
            throw new IllegalArgumentException("a position weighed by a line this is not over: "
                    + NumericTerms.inOrder(weighed) + " against "
                    + NumericTerms.inOrder(wrote.direction().keySet()));
        }
        weighed = Set.copyOf(weighed);
    }

    /**
     * Every line one step from the one the model wrote, each named once, and whether every step this
     * walked could be composed.
     *
     * <p>A step up and a step down at each position, taken one position at a time. What comes back
     * is what a line <em>is</em> rather than what the step was written as, so two steps landing on
     * one direction are one line here — {@code -2 * x + y} weighed one less at {@code x} is
     * {@code -1 * x + y}, and so is weighing {@code y} one more, and a reader told about both would
     * be told one thing twice.
     *
     * <p>A step that leaves nothing weighed at all is no line and is not among these. A step that
     * lands back on the model's own direction is not either: the family is the lines this one is
     * not.
     *
     * <p><b>And a step a model's own decimals put out of the exact arithmetic's reach is a third
     * thing again</b>, told apart from both: a family short one of these is not the whole of what
     * turning every line away establishes, and a caller reading it as though it were — an empty
     * family being no fault domain to state, a family that survived every row being a border no
     * fault this compiler could name touches — would be publishing a settled verdict this walk
     * could not reach. See {@link #everyStepWasComposed}.
     *
     * @param lines               every other line this walk names, none of them the model's own
     * @param everyStepWasComposed whether the exact arithmetic could hold every step tried, whole
     *                            family or not
     */
    public record Found(List<QuantityKey> lines, boolean everyStepWasComposed) {

        public Found {
            lines = List.copyOf(lines);
        }
    }

    public Found others() {
        Set<String> named = new LinkedHashSet<>();
        named.add(wrote.key());
        List<QuantityKey> out = new ArrayList<>();
        boolean everyStepWasComposed = true;
        // In an order the terms settle rather than the one a direction happens to be held in. What
        // a quantity is over is a set, and a caller taking the first of these is a report naming one
        // of them — so a walk in the map's own order would name a different line from one run to
        // the next, and a document written twice could not be compared with itself.
        for (NumericTerm term : weighed.stream()
                .sorted(Comparator.comparing(NumericTerm::toString)).toList()) {
            for (ExactRatio step
                    : List.of(ExactRatio.ONE,
                            ExactRatio.ONE.negated())) {
                Weighed found = weighed(term, step);
                if (!found.composed()) {
                    everyStepWasComposed = false;
                    continue;
                }
                QuantityKey other = found.line();
                if (other != null && named.add(other.key())) {
                    out.add(other);
                }
            }
        }
        return new Found(out, everyStepWasComposed);
    }

    /** What one step of the walk came to: a line, none because the step left nothing weighed
     *  anywhere, or the step not composed at all because the exact arithmetic could not hold a
     *  weight it needed. */
    private record Weighed(QuantityKey line, boolean composed) {}

    /** The same direction with {@code term} weighed {@code step} more, as the line it is. */
    private Weighed weighed(NumericTerm term, ExactRatio step) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (Map.Entry<NumericTerm, ExactRatio> each : NumericTerms.entriesInOrder(wrote.direction())) {
            ExactRatio moved = each.getKey().equals(term)
                    ? each.getValue().plus(step).orNull() : each.getValue();
            if (moved == null) {
                return new Weighed(null, false);
            }
            // A position weighed nothing is a position the line is not over, and is left out rather
            // than carried as a zero: what a line is over is what it names, and a direction holding
            // a weight of nothing would be told from the same line without it.
            if (moved.signum() != 0) {
                coefs.put(each.getKey(), moved);
            }
        }
        return new Weighed(coefs.isEmpty() ? null
                : QuantityKey.of(new LinearForm<>(ExactRatio.ZERO, coefs)), true);
    }
}
