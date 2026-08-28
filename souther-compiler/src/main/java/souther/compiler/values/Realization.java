package souther.compiler.values;

/**
 * What a position's plan came to, or that this compiler would not build it.
 *
 * <p>Two arms and not a set with a flag beside it. An exact answer is a set every reader may use as
 * what the rules leave; the other is not a set at all — what a reader has then is that the rules
 * were understood and their answer was not worked out, and the widest thing true of the position is
 * the only set anybody may hold. Written as a set and a boolean, the two travel separately and one
 * of them arrives alone.
 *
 * <p><b>Nothing here names a rule.</b> This is the whole of what a position admits, met out of every
 * rule that reached it, so running out is a fact about the answer: two patterns each affordable
 * apart have a meet that is not, and neither of them is a rule anybody could rewrite to make it
 * fit. What a single written rule failed at is said before this — a pattern that could not be read,
 * or one whose own machine was more than a rule is allowed — and that failure does name the rule it
 * is about.
 */
public sealed interface Realization {

    /** The set the rules leave, worked out. */
    record Exact(ValueSet set) implements Realization {

        public Exact {
            if (set == null) {
                throw new IllegalArgumentException("an exact answer is some set");
            }
        }
    }

    /**
     * The rules were understood and what they leave was not built.
     *
     * <p>Carries nothing. There is no rule to name and no smaller set to offer: a reader is owed
     * that the answer is unknown, and every value is what is known instead.
     */
    record TooCostly() implements Realization {}

    /** What is known about the position either way, which is the set or every value. */
    default ValueSet upperBound() {
        return this instanceof Exact it ? it.set() : ValueSet.ANY;
    }

    /** Whether the rules' own answer is what came back. */
    default boolean isExact() {
        return this instanceof Exact;
    }
}
