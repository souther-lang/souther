package souther.compiler.check;

import souther.compiler.numeric.NumericDomain;

import java.util.List;
import java.util.Set;

/**
 * How much of what the rules say the bounds a reading produced are able to state.
 *
 * <p>Evidence about the projection that was made, and not a classification of the rules that might
 * have made it. What an edge stands on is that the range is exact: a row at an edge is a whole value
 * with that edge in it, so a rule the bounds cannot express is a way that value can be refused
 * however plainly the numbers themselves were read. Asked of the reading that built the bounds
 * because that is what the answer is about — a second walk of the declarations asking which clauses
 * could have become a bound answers with what this compiler's interval algebra happens to hold, and
 * would go on saying a rule was unread after a domain that holds it was written.
 *
 * <p>Not a coverage question, and the two are independent in both directions. {@code value /= 0} is
 * taken in whole by the reading that turns clauses into sets of values — every question about which
 * values may stand at the position is answered — and the range still admits the 0. {@code value * 2
 * >= 4} moves the floor and is answered as well. A measure that read either off the other would be
 * right wherever they agree and would promise a row nobody can build wherever they do not.
 */
public sealed interface ProjectionEvidence {

    /** Everything the rules say about the positions they name is in the bounds. */
    record Exact() implements ProjectionEvidence {}

    /**
     * The bounds are wider than the rules are, and why.
     *
     * <p>Every cause is a reason some value the bounds admit may be one nothing can build. They are
     * kept apart rather than counted because they are lifted by different work, and a reader sending
     * an author somewhere needs to know which.
     *
     * @param causes never empty: nothing to say is {@link Exact}, which says so
     */
    record Approximate(List<Cause> causes) implements ProjectionEvidence {

        public Approximate {
            causes = List.copyOf(causes);
            if (causes.isEmpty()) {
                throw new IllegalArgumentException("no cause is `Exact`, which says so");
            }
        }
    }

    /**
     * Why a projection is wider than the rules.
     *
     * <p>The three do not share a key, and giving them one would put a rule's name on something that
     * has none. A clause that could not be stated is one whose position is exactly what is unknown
     * about it; a clause that reached the reading is a rule something can be attributed to.
     */
    sealed interface Cause {

        /**
         * A rule of this value never reached the reading that builds the bounds.
         *
         * <p>Either it could not be stated or the walk did not go where it is written. Which rule it
         * was is not said, because at the point this is known there is nothing to say: what is known
         * is the position the stop happened at, and everything under it.
         *
         * <p>Only the stops a construction cannot get out of. A stop taken because the value need
         * not be made — an optional, a collection, a type already met on the way down — leaves
         * rules that refuse nothing at an edge of a field every value has, and what a position
         * admits is short for them all the same. Which of the two a stop was is said where it is
         * taken ({@link InvariantChecker.Borne}), because the one string it reports cannot be read
         * back for it.
         */
        record Unavailable(String path) implements Cause {

            public Unavailable {
                if (path == null) {
                    throw new IllegalArgumentException("a stop happened somewhere");
                }
            }
        }

        /**
         * A rule reached the reading and no numeric constraint over the position came of it.
         *
         * <p>Which is not the same as nothing having read it. {@code value == 3 || value == 5} is
         * held whole by the reading of values, and what the interval algebra is given is the fact
         * keyed on the comparison rather than a form it can narrow by — so the projection is
         * {@code [3, 5]} and the 4 between them is a row nobody can write. A rule read about an atom
         * standing for an arithmetic this cannot carry is here as well: {@code Int.abs(value) >= 2}
         * states a relation, and not one about the position.
         */
        record Unrepresented(RuleRef rule, String path) implements Cause {

            public Unrepresented {
                if (rule == null || path == null) {
                    throw new IllegalArgumentException("a rule left a position unrepresented");
                }
            }
        }

        /**
         * A rule was given to the interval algebra, which could not hold all of it.
         *
         * <p>The domain's own account of what it dropped, at the atom it dropped it about. A
         * disequality is the one an author meets: it is a disjunction, and a range is what this
         * holds — except where one side is already out, which is why {@code value >= 1} written
         * beside {@code value /= 0} leaves nothing lost at all.
         */
        record Lossy(RuleRef rule, FactSubject atom, Set<NumericDomain.Loss> losses)
                implements Cause {

            public Lossy {
                losses = Set.copyOf(losses);
                if (rule == null || atom == null) {
                    throw new IllegalArgumentException("a loss happened to a rule at an atom");
                }
                if (losses.isEmpty()) {
                    throw new IllegalArgumentException("a loss with nothing lost is not one");
                }
            }
        }
    }

    /** Whether an edge may be promised on the strength of these bounds. */
    default boolean isExact() {
        return this instanceof Exact;
    }

    /** The causes, for a reader that only counts them. */
    default List<Cause> causes() {
        return this instanceof Approximate approximate ? approximate.causes() : List.of();
    }
}
