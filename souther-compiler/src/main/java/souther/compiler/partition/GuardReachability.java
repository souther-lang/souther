package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.NumericDomain;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The arms of a body that the model's own rules prove nothing reaches.
 *
 * <p>One fact, derived once, read by every measure. What a position is divided into, which lines are
 * owed a row, which arms are owed a row and which cases the signature is owed are four projections of
 * one universe of possible executions, and four derivations of what is possible are four chances to
 * disagree — which is how a report came to drop the class beyond a cap while still asking for the arm
 * behind it.
 *
 * <p>Independent of the partitioning it happens to be computed beside. A caller with the edges of a
 * body and what its positions can hold has everything this needs, and nothing about a partition is
 * involved in the answer.
 *
 * <p>Only proof excludes. An arm this does not name may still be unreachable — a rule outside what
 * the bounds could hold can refuse every value of an overlap — and that direction is the safe one: an
 * arm left in is one the report asks for, and an author reading an obligation they cannot meet has at
 * least been told something true about their model.
 */
public final class GuardReachability {

    /** Nothing proven: every arm is owed whatever it was owed. */
    public static final GuardReachability NONE = new GuardReachability(Set.of());

    private final Set<Integer> unreachable;

    private GuardReachability(Set<Integer> unreachable) {
        this.unreachable = unreachable;
    }

    /**
     * <p>Held by probe number, which is what a branch obligation is counted by: the sites of a module
     * are numbered across all of its bodies, so one number names one arm of one behavior and a caller
     * matching on it cannot reach another behavior's. Which behavior an edge is in is on the edge
     * itself, for a caller that needs to say.
     *
     * @param edges      both arms of every guard whose comparison could be read
     * @param admissible what the values of each term can be, keyed by the term — which is
     *                   {@code Partitions.Partitioning#domains()}, and any other reading of the same
     *                   question
     */
    public static GuardReachability of(List<GuardEdge> edges,
                                       Map<NumericTerm, NumericDomain.Bounds> admissible) {
        Set<Integer> out = new LinkedHashSet<>();
        for (GuardEdge edge : edges) {
            if (edge.provenDisjoint(admissible.get(edge.term()))) {
                out.add(edge.site());
            }
        }
        return out.isEmpty() ? NONE : new GuardReachability(Set.copyOf(out));
    }

    /**
     * The same, with these arms no longer proven.
     *
     * <p>What takes a proof away is a row that went through the arm. Nothing about the model is wrong
     * then — the proof is — and a caller reading this afterwards has to be told the same thing every
     * other caller is, or the arm leaves one denominator and stays out of another.
     */
    public GuardReachability without(Set<Integer> sites) {
        if (sites.isEmpty() || unreachable.isEmpty()) {
            return this;
        }
        Set<Integer> left = new LinkedHashSet<>(unreachable);
        left.removeAll(sites);
        return left.isEmpty() ? NONE : new GuardReachability(Set.copyOf(left));
    }

    /** Whether nothing reaches the arm with this probe number. */
    public boolean provenUnreachable(int site) {
        return unreachable.contains(site);
    }

    /** The arms nothing reaches, by probe number. */
    public Set<Integer> unreachableSites() {
        return unreachable;
    }

    public boolean isEmpty() {
        return unreachable.isEmpty();
    }
}
