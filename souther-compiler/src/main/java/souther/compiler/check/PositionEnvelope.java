package souther.compiler.check;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Where each position must sit, according to every reading beside the one being asked.
 *
 * <p>What a reduced product needs and the whole of what it may have. Each reading of a state holds
 * what it can say in the language it has: the numbers relate positions to each other, the ordering
 * places one against a written value, the values name which ones a position may take. Whether
 * anything satisfies them together is a question none of them is asked, and asking each in turn
 * answers that something does whenever the one asked had nothing to say. So what the others can
 * project onto a position is met into this, and the reading that holds the alternatives is asked
 * against it.
 *
 * <p><b>An envelope and not the solution set.</b> Every entry is a necessary condition on one
 * position: a value satisfying the rules lies inside it, and a value inside it need not satisfy
 * them. Correlations do not survive the projection — {@code x == y} leaves both positions open —
 * so nothing read off this may be reported as what a model admits, and a reading refused by it is
 * refused by something the rules truly require.
 *
 * <p><b>Nothing left is a fact about the whole and not about a position.</b> A state whose rules
 * admit no assignment has no position to name it at: every position is at no value, and a table
 * saying that of each of them would be read as a lack at whichever one somebody looked at first.
 * So it is its own case, and a reader holding one cannot ask it for a position's range at all.
 *
 * @param <A> what a position is called
 */
sealed interface PositionEnvelope<A> {

    /** The rules of some reading admit no assignment, so there is nowhere for any position to be. */
    record NothingIsLeft<A>() implements PositionEnvelope<A> {}

    /** Where each position must sit, with every position not named being one nothing spoke of. */
    record Restrictions<A>(Map<A, PositionRestriction> at) implements PositionEnvelope<A> {

        public Restrictions {
            at = Collections.unmodifiableMap(new LinkedHashMap<>(at));
        }
    }

    /** Nothing outside says anything about any position. */
    static <A> PositionEnvelope<A> nothingSpokenOf() {
        return new Restrictions<>(Map.of());
    }

    /** Where {@code position} must sit, which is nowhere in particular unless something said so. */
    default PositionRestriction at(A position) {
        if (this instanceof Restrictions<A> it) {
            PositionRestriction said = it.at().get(position);
            return said == null ? new PositionRestriction.NotSpokenOf() : said;
        }
        // Asked of a state that has no assignment at all. There is no such thing as where a
        // position sits here, and the caller is one that has already been told so.
        throw new IllegalStateException("nothing is left, so no position is anywhere");
    }

    /** Whether this leaves every position where it already was, so that asking anything against it
     *  is asking the question that was already answered. */
    default boolean saysNothing() {
        return this instanceof Restrictions<A> it
                && it.at().values().stream().allMatch(PositionRestriction::saysNothing);
    }
}
