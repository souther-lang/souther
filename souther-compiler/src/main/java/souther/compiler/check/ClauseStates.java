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
 * <p>Four answers and not a tally of what a reader could do with the clause. Each says what the
 * clause is about; none of them says whether this compiler managed anything with it, which is the
 * other question and is settled by whichever reading answered.
 *
 * <p>Each carries what it is about, taken from the same reading. Worked out again where the
 * questions are raised, the subject a question is filed under and the subject the reading found
 * would be two answers about one clause.
 */
sealed interface ClauseStates {

    /**
     * Where the values stop: a comparison of the number against one written out.
     *
     * @param position whose values the rule bounds
     * @param line     the number the end is on, which is the position's own value or a count taken
     *                 of it
     */
    record AnEnd(Owed.Subject position, Owed.Subject line) implements ClauseStates {}

    /**
     * That the position holds no value at all.
     *
     * <p>An end past the last value of the order, which is a rule this read perfectly. It raises no
     * line — there is no value to write a row at — and it is not a rule left unread either.
     */
    record NoValueAtAll(Owed.Subject position) implements ClauseStates {}

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
     * @param positions the ones the clause names. A rule cannot cost a position it does not name, so
     *                  these and not every position of the value. Where it names none this reading
     *                  recognised, the value itself stands: what the clause is about is then not
     *                  known, and filing it nowhere would let a rule this could not place take
     *                  nothing with it
     */
    record SomethingElse(Set<Owed.Subject> positions) implements ClauseStates {

        public SomethingElse {
            // Insertion order: `Set.of` and `Set.copyOf` iterate in an order salted once per JVM
            // run, and what is built from these reaches a checked-in document.
            positions = positions.isEmpty()
                    ? java.util.Collections.unmodifiableSet(new java.util.LinkedHashSet<>(
                            java.util.List.of(Owed.Subject.at(FieldDomains.THE_VALUE))))
                    : java.util.Collections.unmodifiableSet(
                            new java.util.LinkedHashSet<>(positions));
        }

        static SomethingElse naming(List<Owed.Subject> found) {
            return new SomethingElse(new java.util.LinkedHashSet<>(found));
        }
    }
}
