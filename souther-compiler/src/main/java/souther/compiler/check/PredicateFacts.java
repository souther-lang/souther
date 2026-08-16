package souther.compiler.check;

import java.util.HashSet;
import java.util.Set;

/**
 * The predicates the guards have settled on the current path, each keyed by a canonical rendering of
 * the call that states it (see {@link InvariantChecker}). A predicate that is not a comparison —
 * {@code List.allDistinctBy}, {@code List.contains}, {@code String.matches} — holds no numeric relation
 * and so has nowhere to live in {@link souther.compiler.numeric.NumericDomain}; this is where it lives instead.
 *
 * <p>Nothing here reasons: two predicates relate only by being the same key. What that buys is the
 * guarantee the discharge check needs — a construction whose invariant states a predicate is
 * discharged by a guard stating the same predicate of the same term, and reported when there is
 * none. Immutable, threaded functionally alongside the numeric domain.
 */
final class PredicateFacts {

    private static final PredicateFacts NONE = new PredicateFacts(false, Set.of(), Set.of());
    private static final PredicateFacts BOTTOM = new PredicateFacts(true, Set.of(), Set.of());

    private final boolean bottom;    // contradictory guards — this path is not taken
    private final Set<Term> holds;
    private final Set<Term> fails;

    private PredicateFacts(boolean bottom, Set<Term> holds, Set<Term> fails) {
        this.bottom = bottom;
        this.holds = holds;
        this.fails = fails;
    }

    static PredicateFacts none() {
        return NONE;
    }

    /**
     * Whether the predicates settled here cannot all hold.
     *
     * <p>A claim about the values and not about the reading: what it takes to reach it is one key
     * settled both ways, which is a contradiction whatever the predicate says. So it is read where a
     * value is asked for as well as where a path is — a declaration stating a predicate of its value
     * and denying the same predicate of the same value has no value, and nothing about that answer
     * needs the numbers.
     */
    boolean isBottom() {
        return bottom;
    }

    /** The facts with {@code key} settled. Settling it both ways makes the path infeasible. */
    PredicateFacts assume(Term key, boolean positive) {
        if (bottom) {
            return this;
        }
        if ((positive ? fails : holds).contains(key)) {
            return BOTTOM;
        }
        Set<Term> next = new HashSet<>(positive ? holds : fails);
        next.add(key);
        return positive
                ? new PredicateFacts(false, Set.copyOf(next), fails)
                : new PredicateFacts(false, holds, Set.copyOf(next));
    }

    /** Whether the guards prove {@code key} (or its negation, when {@code positive} is false). */
    boolean entails(Term key, boolean positive) {
        return bottom || (positive ? holds : fails).contains(key);
    }

    /** Whether the guards prove the opposite of what {@code positive} asks of {@code key}. */
    boolean refutes(Term key, boolean positive) {
        return !bottom && (positive ? fails : holds).contains(key);
    }

}
