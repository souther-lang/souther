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
         * A rule was given to the interval algebra, and what the algebra projects does not hold it.
         *
         * <p>A disequality is the one an author meets: it is a disjunction, and a range is what this
         * holds — except where one side is already out, which is why {@code value >= 1} written
         * beside {@code value /= 0} leaves the bounds stating both.
         *
         * <p>Both the rule and what went unstated about it are this rule's. Two rules leaving one
         * position short in different ways are two causes saying two different things, rather than
         * one account of the position that both are filed under.
         */
        record Lossy(RuleRef rule, FactSubject atom, Set<Unstated> unstated) implements Cause {

            public Lossy {
                unstated = Set.copyOf(unstated);
                if (rule == null || atom == null) {
                    throw new IllegalArgumentException("something went unstated about a rule at an atom");
                }
                if (unstated.isEmpty()) {
                    throw new IllegalArgumentException("nothing unstated is not a cause");
                }
            }
        }

        /**
         * An end the rules put at a value no decimal writes, so the number handed over is a hair
         * outside where they stop.
         *
         * <p>Its own cause and not one of {@link Lossy}'s kinds, because it is not about a rule. The
         * reasoning reached the position's edge exactly; what could not carry it is the writing. A
         * reader placing a row at an edge is the one this is for — the edge it is given is not the
         * edge the rules drew.
         *
         * <p>Rare. An end on a position whose values step is a whole number, and one on a position
         * whose values fill is a decimal unless a rule divided by something ten is not made of.
         */
        record Rounded(FactSubject atom) implements Cause {

            public Rounded {
                if (atom == null) {
                    throw new IllegalArgumentException("a rounded end is an end of something");
                }
            }
        }

        /**
         * What a range at one position could not state of a rule about it.
         *
         * <p>Worked out from the rule and from what the rules were found to leave, rather than
         * recorded as each rule arrived. Recorded, it was a history: a rule that narrowed nothing at
         * the moment it was read left a mark that stayed after a later rule made it bite, so a range
         * that had become the whole of what the rules say still carried a note that it was not.
         */
        enum Unstated {

            /**
             * A rule holding the position away from a value inside its range.
             *
             * <p>Only where it is inside. A hole at an edge moves the edge and is then something the
             * range does state — {@code value /= 0} beside {@code value >= 0} leaves the position at
             * one and nothing is left over.
             */
            A_HOLE,

            /**
             * A rule relating this position to others, which a range at one of them cannot carry.
             *
             * <p>Only where the ranges do not already hold it. What such a rule leaves each position
             * it names is derived and is in the bounds; what a range cannot say is the relation, and
             * it only needs saying where a value of each range can be picked that together break it.
             */
            A_RELATION
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
