package souther.compiler.check;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which coverage obligations one rule of the model raises.
 *
 * <p>Two answers and not a set that may be empty. A rule raising none is a conclusion about the rule
 * — it was read, and what it says raises no question a measure of coverage answers — and an empty
 * set is what a classification that had never looked would also produce. Written as a set, the arm
 * a new rule shape falls into on the day it is added is "raises nothing", so the rule is reported as
 * fully accounted for by nobody having asked; written as two answers, that arm has to be reached on
 * purpose.
 *
 * <p>{@link Irrelevant} cannot be written down. It is reached only by classifying a
 * {@link ClauseStates}, which is package-private and comes only from a reader that looked at the
 * clause — the same arrangement {@code UndividedPosition.Why.Absent} is under, and for the same
 * reason: the sentence that costs the most to be wrong about is the one that has to cost something
 * to say.
 *
 * <p>No verdict here. What is raised and what answered it are different questions asked at different
 * times, and a rule that raises an obligation nothing answers is exactly what a report is for — so
 * an obligation is a node and whether it was discharged is written beside it, never into it.
 */
public sealed interface Required {

    /** The questions, which is empty exactly where the rule raises none. */
    Set<Owed> obligations();

    /**
     * The rule raises these, and there is at least one.
     *
     * <p>A private constructor, so that the only way to a value of this is through a classification
     * of what some reader found the clause to state. Assembled by hand, a caller could raise an
     * obligation the model never wrote, or drop one it did.
     */
    final class Some implements Required {

        private final Set<Owed> obligations;

        private Some(Set<Owed> obligations) {
            if (obligations.isEmpty()) {
                throw new IllegalArgumentException(
                        "a rule that raises nothing is a different answer");
            }
            this.obligations = Collections.unmodifiableSet(new LinkedHashSet<>(obligations));
        }

        @Override
        public Set<Owed> obligations() {
            return obligations;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Some some && obligations.equals(some.obligations);
        }

        @Override
        public int hashCode() {
            return obligations.hashCode();
        }

        @Override
        public String toString() {
            return obligations.toString();
        }
    }

    /**
     * The rule was read, and it raises no question a measure of coverage answers.
     *
     * <p>Not "nothing was found". A rule relating two positions says where one stands against
     * another, which is a rule about a pair; a partition is of one position and a line is on one
     * number, so neither is a question this rule left open. Read as a rule nothing accounted for, a
     * model whose every rule is fine would be reported as one this compiler could not read.
     */
    final class Irrelevant implements Required {

        private final Because because;

        private Irrelevant(Because because) {
            this.because = because;
        }

        /** What settled it. */
        public Because because() {
            return because;
        }

        @Override
        public Set<Owed> obligations() {
            return Set.of();
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Irrelevant it && because == it.because;
        }

        @Override
        public int hashCode() {
            return because.hashCode();
        }

        @Override
        public String toString() {
            return "Irrelevant(" + because + ")";
        }
    }

    /**
     * Why a rule raises no coverage obligation.
     *
     * <p>Kept rather than collapsed to the fact, because a reader acting on one of these is doing
     * different work, and because an arm nothing produces is how a classification quietly stops
     * covering a shape.
     */
    enum Because {

        /** The rule is about how one position stands against another, which no partition of one and
         * no line on one number is. */
        IT_RELATES_TWO_POSITIONS,

        /**
         * The rule names no position of this value.
         *
         * <p>{@code invariant t = 1 >= 0} says nothing about anywhere, so there is nothing about a
         * position for anything to have read. A rule cannot cost a position it does not name, which
         * is what the reading of values says of its own failures for the same reason.
         */
        IT_NAMES_NO_POSITION
    }

    /** What every invariant clause raises about a position it is written about. */
    private static Owed admittedValues(Owed.Subject where) {
        return new Owed(CoverageObligation.ADMITTED_VALUES, where);
    }

    /**
     * What an invariant clause raises, from what a reader found it to state.
     *
     * <p>One switch and no {@code default}, so a shape added and not classified stops the build
     * rather than arriving here as the arm that happens to be nearest.
     *
     * <p>Every arm but one starts from {@code ADMITTED_VALUES}. That is what an invariant is: a rule
     * about which values may stand somewhere, whichever shape it is written in and whether or not
     * this compiler can read it. What the shape decides is what it raises <em>besides</em> that.
     */
    static Required ofInvariant(ClauseStates states) {
        return switch (states) {
            // An end is a statement about the values and a line rows are owed at, both — and the
            // two are about different subjects, which is why they are carried apart.
            // A `LinkedHashSet` and not `Set.of`, which iterates in an order salted once per JVM
            // run — the questions reach a document in the order they are written here.
            case ClauseStates.AnEnd end -> new Some(new LinkedHashSet<>(java.util.List.of(
                    admittedValues(end.position()),
                    new Owed(CoverageObligation.BOUNDARY, end.line()))));
            // No line: there is no value to write a row at. The rule still says which values may
            // stand there, and what it says is that none may.
            case ClauseStates.NoValueAtAll none -> new Some(new LinkedHashSet<>(
                    java.util.List.of(admittedValues(none.position()))));
            // A clause about no position of this value raises no question about one. Not a rule
            // that went unread: what it says was read, and what it says is about nothing here.
            case ClauseStates.SomethingElse other -> other.positions().isEmpty()
                    ? new Irrelevant(Because.IT_NAMES_NO_POSITION)
                    : new Some(other.positions().stream()
                            .map(Required::admittedValues).collect(java.util.stream.Collectors
                                    .toCollection(LinkedHashSet::new)));
            case ClauseStates.ARelation _ -> new Irrelevant(Because.IT_RELATES_TWO_POSITIONS);
        };
    }

    /**
     * Both, for a clause read one conjunct at a time.
     *
     * <p>A conjunction is one rule the author wrote, and what it raises is what its parts raise
     * together. {@link Irrelevant} is the identity: {@code a < b && value >= 1} raises the end's
     * questions, and the relational half taking them away would lose a line the author drew.
     */
    static Required and(Required had, Required one) {
        if (had == null) {
            return one;
        }
        if (had instanceof Irrelevant) {
            return one instanceof Irrelevant ? had : one;
        }
        if (one instanceof Irrelevant) {
            return had;
        }
        Set<Owed> both = new LinkedHashSet<>(had.obligations());
        both.addAll(one.obligations());
        return new Some(both);
    }
}
