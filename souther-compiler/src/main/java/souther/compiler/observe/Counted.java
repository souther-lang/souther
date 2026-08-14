package souther.compiler.observe;

import java.util.Set;

/**
 * What this compile's own counting read of one row's evaluation.
 *
 * <p>Both numbers are about code the emitter counted into, which is what this compile generated and
 * nothing else. That is the whole of what they cover and it is not the same as the application: a
 * fixture applies the helpers it names before the behavior is reached, so a row that never applied
 * the behavior can still have spent counted points, and a row applied through something this compile
 * did not generate spends none inside the application while its fixtures spend what they spend.
 * {@link Applied} is what says which of those a row is.
 *
 * <p>{@link #steps} is what the row cost in the unit it is held to, so a build can see how much of
 * the budget its rows use before one of them reaches it — the only way to set the budget from
 * evidence rather than by guessing. Zero says no counted point was passed, which a row that ran a
 * body with no loop in it does as much as one that never ran anything: {@link Disposition} is what
 * tells those apart, and it is also what says a zero is a reading that was never taken, since a
 * count read off a worker still running would be some of what it spent rather than what it spent.
 *
 * <p>{@link #hits} is the branch sites the row went through. Empty until branches are measured, which
 * is a property of the compile rather than of the row.
 */
public record Counted(long steps, Set<Integer> hits) {

    public Counted {
        hits = hits == null ? Set.of() : Set.copyOf(hits);
    }
}
