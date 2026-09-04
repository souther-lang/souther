package souther.compiler.values;

/**
 * What a position's plan came to, or which limit stopped this compiler building it.
 *
 * <p>Arms and not a set with a flag beside it. An exact answer is a set every reader may use as what
 * the rules leave; the others are not sets at all — what a reader has then is that the rules were
 * understood and their answer was not worked out, and the widest thing true of the position is the
 * only set anybody may hold. Written as a set and a boolean, the two travel separately and one of
 * them arrives alone.
 *
 * <p><b>Two ways of not being built, because they are owed to different people.</b> One pattern
 * larger than any machine this holds is a rule somebody wrote and can write differently, and saying
 * so names the rule. An answer that has spent its allowance is not about any one rule: the same
 * pattern asked for first would have been made, and naming the rule that happened to be last tells
 * an author to rewrite something that is not why.
 *
 * <p><b>And nothing here names one.</b> Which rule asked for a leaf is not a thing a leaf knows —
 * the same pattern in three rules is one machine — so the name is put on by whoever asked. What is
 * answered here is which limit refused, and the asking occurrence says whose failure that is.
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
     * One machine came to more states than a machine may have.
     *
     * <p>About what was being built and not about how much was left: the same thing asked for
     * first, out of a full allowance, would have been refused the same way. Where what was being
     * built is one pattern an author wrote, that is a fact about the pattern.
     *
     * <p><b>So it names the pattern, and the pattern is the one that asked.</b> Every rule reaching
     * a position pays into one allowance, so the position is what the spending is arranged by and
     * is not what any of it is about. Read back from there, this became a fact about every rule
     * that mentions the place — which sends an author to a clause that reads perfectly well, and
     * leaves the reason with no place among the parts they wrote.
     *
     * @param occurrence the written pattern whose machine was refused
     */
    record OverTheMachineLimit(AuthoredOccurrence occurrence) implements Realization {

        public OverTheMachineLimit {
            if (occurrence == null) {
                throw new IllegalArgumentException(
                        "a machine is asked for by something somebody wrote, and this says which");
            }
        }
    }

    /**
     * What this answer has built came to more than it may build in all.
     *
     * <p>About the answer. Every rule that reached the position was understood and every one of
     * them could have been built; what ran out is the allowance for all of them together, and which
     * one was being built when it ran out is a fact about the order and not about the rules.
     */
    record OverTheAnswerLimit() implements Realization {}

    /** What is known about the position either way, which is the set or every value. */
    default ValueSet upperBound() {
        return this instanceof Exact it ? it.set() : ValueSet.ANY;
    }

    /** Whether the rules' own answer is what came back. */
    default boolean isExact() {
        return this instanceof Exact;
    }
}
