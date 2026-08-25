package souther.compiler.check;

import java.util.List;
import java.util.Set;

/**
 * What one clause of an invariant states, as the reading that ran over it found it.
 *
 * <p>The input the obligations a clause raises are a function of, and package-private so that they
 * stay one: a value of this comes from a reader that looked at the clause, and outside this package
 * there is no way to make one. Which is what keeps {@link Required.Irrelevant} from being a sentence
 * anybody can write — saying that a rule raises no question at all is a conclusion about the model,
 * and the only thing entitled to draw it is a reading of the rule.
 *
 * <p>Three answers and not a tally of what a reader could do with the clause. Each says what the
 * clause is about; none of them says whether this compiler managed anything with it, which is the
 * other question and is {@link InvariantBound.Read}'s. The two used to be one: {@code AnEnd} was
 * built where {@code InvariantBound.at} came back with an end, so a bound this could not fold — the
 * {@code 20} in {@code value <= 10 * 2} — arrived here as a clause that states no bound at all.
 * {@code NoValueAtAll} was the same mixing from the other side, reached only by folding the bound
 * and comparing it against the carrier's order.
 *
 * <p>Each carries what it is about, taken from the same reading. Worked out again where the
 * questions are raised, the subject a question is filed under and the subject the reading found
 * would be two answers about one clause.
 *
 * <p><b>What a clause is about, and not the questions it raises.</b> A position it names is a path
 * and a line it draws is a {@link FieldDomains.Coordinate}, which are what a reading of a clause
 * has; which coverage question each of them becomes is {@link Required#ofInvariant}'s and is
 * decided there. Written in the vocabulary of the questions instead, the positions were a set of
 * subjects every member of which was the same arm with the same flag — a set of paths wearing the
 * type of a set of subjects, so that a lookup by path read as a comparison of subjects.
 */
sealed interface ClauseStates {

    /**
     * Where the values stop: a coordinate compared for order against an expression naming no
     * coordinate of this value.
     *
     * <p>Whether an end came of it is not asked here, and neither is whether the order has a value
     * at the end. A rule states where the values stop by being written that way; what this compiler
     * made of the number on the other side is what answers the question, not what raises it.
     *
     * @param line      the number the end is on, which is the position's own value or a number an
     *                  operation answers of it. The operation itself, since two operations over one
     *                  path are two lines and a flag saying one was taken cannot tell them apart
     * @param positions the ones the clause is about, which is what a rule can cost. Never empty:
     *                  a clause bounding a coordinate names the position it sits at
     */
    record ABound(FieldDomains.Coordinate line, Set<String> positions) implements ClauseStates {

        public ABound {
            if (line == null) {
                throw new IllegalArgumentException("a bound is a line on some number");
            }
            if (positions.isEmpty()) {
                throw new IllegalArgumentException("a bound is written about a position");
            }
            positions = java.util.Collections.unmodifiableSet(
                    new java.util.LinkedHashSet<>(positions));
        }
    }

    /**
     * How this position stands against another.
     *
     * <p>{@code startsAt < endsAt}, {@code a /= b}. Nothing about it was beyond the reading — both
     * sides were recognised — and a set of one position's values is not what it says, so it raises
     * no question about one position. What it settles is settled beside the partition rather than in
     * it (ADR-0090).
     */
    record ARelation() implements ClauseStates {}

    /**
     * Something else: the values a rule names, a call, a pattern, an expression the terms do not
     * name.
     *
     * <p>One arm for all of them, because what a clause raises does not turn on which of them it is.
     * A rule about a position's values is a rule about its values whether this compiler can read it
     * or not, and reading the arm as "this compiler failed" is the confusion the whole type exists
     * to stop: the question is raised by the model, and whether anything answered it is asked
     * afterwards.
     *
     * @param positions the ones the clause names, which may be none. A rule cannot cost a position
     *                  it does not name, so these and not every position of the value — and a
     *                  clause naming none of them raises no question about one, which is what
     *                  {@link Required#ofInvariant} makes of an empty set. Filed at the value
     *                  instead, {@code invariant t = 1 >= 0} was a rule nothing had accounted for
     */
    record SomethingElse(Set<String> positions) implements ClauseStates {

        public SomethingElse {
            // Insertion order: `Set.of` and `Set.copyOf` iterate in an order salted once per JVM
            // run, and what is built from these reaches a checked-in document.
            positions = java.util.Collections.unmodifiableSet(
                    new java.util.LinkedHashSet<>(positions));
        }

        static SomethingElse naming(List<String> found) {
            return new SomethingElse(new java.util.LinkedHashSet<>(found));
        }
    }

    /** The positions this clause is about, by which a rule can cost one. */
    default Set<String> about() {
        return switch (this) {
            case ABound bound -> bound.positions();
            case SomethingElse other -> other.positions();
            // A rule about a pair costs neither of them: what it says is not a set of one
            // position's values, so there is nothing about one for anything to have read.
            case ARelation _ -> Set.of();
        };
    }
}
