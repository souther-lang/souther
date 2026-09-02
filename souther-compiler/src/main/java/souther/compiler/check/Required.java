package souther.compiler.check;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * Which coverage obligations one rule raises where it applies to one value, in that value's
 * vocabulary.
 *
 * <p><b>Not a property of the rule alone.</b> What is raised is {@link Owed} over a
 * {@link RuleKey}, and a key is relative to the value whose clauses are being read. So one rule
 * read at two values raises questions neither spells the same way — and raises a different number
 * of them wherever a value carries the rule's type more than once: a record with a {@code was} and
 * a {@code now} of one bounded type is held to that type's clause at both places, where the type
 * itself is held to it at one, and a row satisfying it at one says nothing about the other. The
 * count is the model's shape and has nothing to do with how often anything was read.
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
     * <p>Not "nothing was found". A clause about no position of the value says nothing about one,
     * and a rule singling a value out of two things that both move with the row singles it out of
     * neither. Read as rules nothing accounted for, a model whose every rule is fine would be
     * reported as one this compiler could not read.
     *
     */
    final class Irrelevant implements Required {

        private final Set<Because> because;

        private Irrelevant(Set<Because> because) {
            this.because = Collections.unmodifiableSet(new LinkedHashSet<>(because));
        }

        /**
         * What settled it, which is every part's reason and not one of them.
         *
         * <p>{@code value == other && 1 >= 0} raises nothing because one part singles a value out of
         * two things that both move and the other is about nothing here, and both are true of the
         * rule. Kept as one, the answer was whichever part was written first — a fact about the
         * source order under a name that says why the rule raises nothing.
         */
        public Set<Because> because() {
            return because;
        }

        @Override
        public Set<Owed> obligations() {
            return Set.of();
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Irrelevant it && because.equals(it.because);
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

        /**
         * The rule singles a value out of two things that both move with the row, which singles one
         * out of neither.
         *
         * <p>{@code a == b} puts the whole of one arm on the place the two meet, and that arm is a
         * row the branch measure already asks for. Not every rule about a pair: an order across one
         * draws a line, and that is a question raised rather than one nobody has.
         */
        IT_RELATES_TWO_POSITIONS,

        /**
         * The rule names no position of this value.
         *
         * <p>{@code invariant t = 1 >= 0} says nothing about anywhere, so there is nothing about a
         * position for anything to have read. A rule cannot cost a position it does not name, which
         * is what the reading of values says of its own failures for the same reason.
         */
        IT_NAMES_NO_POSITION,

        /**
         * The rule names a position and restricts no value of it.
         *
         * <p>{@code lo - lo >= 0} holds of every row: the quantity it cuts is empty, so there is no
         * value it admits or refuses anywhere and no question a measure of coverage could answer.
         *
         * <p>Its own word beside {@link #IT_NAMES_NO_POSITION}, which is a rule about nothing here
         * at all. This one is written about a position — an author looking for why it costs the
         * measurement nothing would not find it under a word saying their clause mentions no field
         * of the value it is declared on.
         */
        IT_CONSTRAINS_NO_VALUE
    }

    /** What every invariant clause raises about a position it is written about. */
    private static Set<Because> union(Set<Because> these, Set<Because> those) {
        Set<Because> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
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
     *
     * <p><b>Nothing here is asked of a reading.</b> A rule stating where the values stop raises the
     * question about that line by being written that way, and whether this compiler could fold the
     * number on the other side is what answers it. Read off the reading, {@code value <= 20} raised
     * the question and {@code value <= 10 * 2} raised none, and the two state one line — so the
     * accounting came back complete for a rule nothing had taken in (#851).
     */
    static Required ofInvariant(ClauseStates states) {
        return switch (states) {
            // A bound is a statement about the values and a line rows are owed at, both — and the
            // two are about different subjects, which is why they are carried apart.
            // A `LinkedHashSet` and not `Set.of`, which iterates in an order salted once per JVM
            // run — the questions reach a document in the order they are written here.
            case ClauseStates.ABound bound -> {
                Set<Owed> owed = bound.named().stream().map(Owed.AdmittedValues::new)
                        .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
                owed.add(new Owed.Boundary(bound.line()));
                yield new Some(owed);
            }
            // A clause writing no name of this value raises no question about one. Not a rule
            // that went unread: what it says was read, and what it says is about nothing here.
            case ClauseStates.SomethingElse other -> other.named().isEmpty()
                    ? new Irrelevant(Set.of(Because.IT_NAMES_NO_POSITION))
                    : new Some(other.named().stream()
                            .map(Owed.AdmittedValues::new).collect(java.util.stream.Collectors
                                    .toCollection(LinkedHashSet::new)));
            case ClauseStates.ARelation _ -> new Irrelevant(Set.of(Because.IT_RELATES_TWO_POSITIONS));
            case ClauseStates.NoRestriction _ ->
                    new Irrelevant(Set.of(Because.IT_CONSTRAINS_NO_VALUE));
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
        if (had instanceof Irrelevant it) {
            // Both, where both parts raise nothing: each is a reason the rule raises nothing, and
            // keeping one makes the answer turn on which part was written first.
            return one instanceof Irrelevant too
                    ? new Irrelevant(union(it.because(), too.because())) : one;
        }
        if (one instanceof Irrelevant) {
            return had;
        }
        Set<Owed> both = new LinkedHashSet<>(had.obligations());
        both.addAll(one.obligations());
        return new Some(both);
    }
}
