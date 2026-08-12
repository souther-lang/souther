package souther.compiler.numeric;

import java.util.Collection;
import java.util.NavigableSet;
import java.util.TreeSet;

/**
 * The counts worth telling apart, and the rounding that keeps them finite in number.
 *
 * <p>A walk over the type graph that rises until it stops changing stops at all because there are
 * finitely many answers to rise through. Counts written in a model are not finite in that way — a
 * collection asked to hold a million values would give a million answers to climb — so the answers
 * are cut down to the ones some question turns on.
 *
 * <p>Every question a transfer asks of a count has the same shape: is this too small to fill that
 * collection. A collection asking for {@code n} turns on whether the count reaches {@code n - 1} and
 * on nothing finer, so that is what is kept, and a count landing between two of them rises to the
 * higher. Above them all there is nothing left to ask and the answer is
 * {@link Cardinality#UNKNOWN}.
 *
 * <p>Up and never down, so a rounded count claims a type may have more values than was shown. That is
 * the direction that admits: a collection that cannot be filled looks as though it might be, and
 * nothing is refused on the strength of a number that was rounded.
 *
 * <p>Fixed before the walk starts and not added to while it runs. What makes the walk stop is that
 * the answers are finite and settled, and a question discovered mid-walk would give it somewhere new
 * to rise to.
 */
public final class CardinalityCuts {

    private final NavigableSet<Long> kept;

    private CardinalityCuts(NavigableSet<Long> kept) {
        this.kept = kept;
    }

    /**
     * The answers to keep, given what the collections ask for.
     *
     * <p>Each asking count is kept as the count one below it, which is the widest a type can be and
     * still be too small to fill it. An asking count of none keeps nothing: every count fills a
     * collection that asks for nothing.
     */
    public static CardinalityCuts keeping(Collection<Long> asked) {
        NavigableSet<Long> kept = new TreeSet<>();
        for (Long each : asked) {
            if (each != null && each > 0) {
                kept.add(each - 1);
            }
        }
        return new CardinalityCuts(kept);
    }

    /**
     * {@code of} as one of the answers kept, rising to the next one where it is not one of them.
     *
     * <p>Both ends are answers of their own and are never rounded away: having no value is what this
     * whole reading is for, and having no bound is already the widest answer there is.
     */
    public Cardinality round(Cardinality of) {
        if (of.none() || of.unknown()) {
            return of;
        }
        Long at = kept.ceiling(of.boundOr(-1));
        return at == null ? Cardinality.UNKNOWN : Cardinality.atMost(at);
    }

    /** How many answers there are, which is how far the walk can rise. */
    public int answers() {
        return kept.size() + 2;   // and the two ends, which are answers no question keeps
    }
}
