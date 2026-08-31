package souther.compiler.partition;

import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.NumericDomain;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * How many the rules leave the container standing at a position.
 *
 * <p>Read off the input's own reading of its rules, and asked by the position the container stands
 * at. Asked before by spelling a name for the position and looking it up among the fields of the
 * parameter's own type, which only ever found a container that is a field of a record — a container
 * that is a value of its own, and one that stands inside a sequence, have rules no such name
 * reaches. So a list capped at none inside a list left a position under it standing as something to
 * divide, and every combination that position takes part in was offered rows nothing could ever be
 * written for.
 *
 * <p>About the positions of the input and about nothing else. A coordinate of a
 * {@link ConstructionPlan} is spelled with the same {@link TermPath} and is a different thing: the
 * plan goes on past where the reading stops, and puts positions under a sum the declaration has none
 * of. What a plan's node holds is read off that node's own type, which is where its rules are.
 */
public record HeldCounts(Map<TermPath, NumericTerm> sizes) {

    /** Nothing counted, which is what an input with no container in it comes to. */
    public static final HeldCounts NONE = new HeldCounts(Map.of());

    public HeldCounts {
        sizes = Map.copyOf(sizes);
    }

    /**
     * The counts the positions of {@code domain} are measured at.
     *
     * <p>Kept by position rather than solved here: what the rules leave a count is the reading's to
     * answer, and answering it once per position up front would fix the numbers before the row has
     * settled anything.
     */
    public static HeldCounts of(InputDomain domain) {
        Map<TermPath, NumericTerm> sizes = new LinkedHashMap<>();
        for (Position each : domain.positions()) {
            // Counts of containers and nothing else. What this feeds is how many elements to build,
            // so an operation whose number is not how many the value holds has no business bounding
            // it: `Time.hour(t) <= 5` would otherwise be read as a container of at most five. The one
            // question here that names an arm, and it names it because it is about that arm.
            if (each.term() instanceof NumericTerm.TakenOf taken
                    && taken.takenAs() instanceof souther.compiler.semantics.TakenAs.HowManyItHolds) {
                sizes.put(each.path(), each.term());
            }
        }
        return sizes.isEmpty() ? NONE : new HeldCounts(sizes);
    }

    /**
     * How many the rules say the container at {@code at} holds at the most, or every number where
     * they say nothing about how many.
     *
     * <p>{@code counts} is the reading these positions were found in. Held here instead, a caller
     * with a reading of its own could ask what one reading's positions come to under another's
     * rules, and the answer would be about neither.
     *
     * <p>Not visible outside this package, because the pairing is what a subject holds
     * ({@link Generator.Subject#mostHeldAt}) and a caller free to reach this is a caller free to
     * pair it with a reading of its own.
     */
    int most(TermPath at, Quantities counts) {
        NumericTerm term = sizes.get(at);
        if (term == null) {
            return Integer.MAX_VALUE;
        }
        NumericDomain.Bounds runs = counts.runsBetween(term);
        return runs == null ? Integer.MAX_VALUE : CountDomain.mostFrom(runs.max());
    }
}
