package souther.compiler.check;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.function.Function;

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
 *
 * <p>Kept in the order the predicates were settled. Nothing here answers with one of them, and a
 * renaming that has to refuse two subjects under one name names whichever it reaches first — read
 * off a set whose iteration order is salted once per run, which of two collisions is reported would
 * move between runs of the same compiler.
 *
 * @param <A> what a fact is filed under. The subject is the caller's, because one reading's
 *            predicates are met with another's only once both are said in one vocabulary
 */
public final class PredicateFacts<A> {

    private final boolean bottom;    // contradictory guards — this path is not taken
    private final Set<A> holds;
    private final Set<A> fails;

    private PredicateFacts(boolean bottom, Set<A> holds, Set<A> fails) {
        this.bottom = bottom;
        this.holds = held(holds);
        this.fails = held(fails);
    }

    private static <A> Set<A> held(Set<A> of) {
        return Collections.unmodifiableSet(new LinkedHashSet<>(of));
    }

    /** Contradictory guards, which is one key settled both ways however it was reached. */
    private static <A> PredicateFacts<A> bottom() {
        return new PredicateFacts<>(true, Set.of(), Set.of());
    }

    /** Nothing settled either way. */
    public static <A> PredicateFacts<A> none() {
        return new PredicateFacts<>(false, Set.of(), Set.of());
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
    public boolean isBottom() {
        return bottom;
    }

    /** The facts with {@code key} settled. Settling it both ways makes the path infeasible. */
    PredicateFacts<A> assume(A key, boolean positive) {
        if (bottom) {
            return this;
        }
        if ((positive ? fails : holds).contains(key)) {
            return bottom();
        }
        Set<A> next = new LinkedHashSet<>(positive ? holds : fails);
        next.add(key);
        return positive
                ? new PredicateFacts<>(false, next, fails)
                : new PredicateFacts<>(false, holds, next);
    }

    /** Whether the guards prove {@code key} (or its negation, when {@code positive} is false). */
    boolean entails(A key, boolean positive) {
        return bottom || (positive ? holds : fails).contains(key);
    }

    /** Whether the guards prove the opposite of what {@code positive} asks of {@code key}. */
    boolean refutes(A key, boolean positive) {
        return !bottom && (positive ? fails : holds).contains(key);
    }

    /**
     * Both readings settled at once.
     *
     * <p>A predicate one of them holds and the other denies is one key settled both ways, which is
     * the same contradiction reaching this the same way it reaches it from a single reading.
     * Nothing else here relates two predicates, so the rest is the two sets put together.
     */
    public PredicateFacts<A> meet(PredicateFacts<A> other) {
        if (bottom || other.bottom) {
            return bottom();
        }
        Set<A> bothHold = new LinkedHashSet<>(holds);
        bothHold.addAll(other.holds);
        Set<A> bothFail = new LinkedHashSet<>(fails);
        bothFail.addAll(other.fails);
        return bothHold.stream().anyMatch(bothFail::contains)
                ? bottom() : new PredicateFacts<>(false, bothHold, bothFail);
    }

    /**
     * The same facts about the same predicates, under the names {@code naming} gives their subjects.
     *
     * <p>The naming has to name two subjects two subjects. Two of them arriving under one name would
     * be one predicate settled by two readings that never said anything about each other, and where
     * one holds it and the other denies it this would come out contradictory over a disagreement
     * nobody wrote. Which is not checked here — this sits below the package that owns a whole
     * vocabulary — and is what {@link InjectiveRenaming} is, handed over by
     * {@link ConstraintState#renamed}. Every subject held here passes through the naming, so a
     * caller holding one of those sees all of them.
     */
    public <B> PredicateFacts<B> renamed(Function<A, B> naming) {
        if (bottom) {
            return bottom();
        }
        Set<B> outHolds = new LinkedHashSet<>();
        holds.forEach(key -> outHolds.add(naming.apply(key)));
        Set<B> outFails = new LinkedHashSet<>();
        fails.forEach(key -> outFails.add(naming.apply(key)));
        return new PredicateFacts<>(false, outHolds, outFails);
    }
}
