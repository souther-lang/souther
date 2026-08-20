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
     * <p>Not "nothing was found". A clause about no position of the value says nothing about one,
     * and a rule singling a value out of two things that both move with the row singles it out of
     * neither. Read as rules nothing accounted for, a model whose every rule is fine would be
     * reported as one this compiler could not read.
     *
     * <p>Narrower than it was. A rule relating two positions used to be here whatever it stated,
     * and an order across such a pair draws a line where they hold one count — a question this
     * raises now, about the comparison that drew it.
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
        IT_NAMES_NO_POSITION
    }

    /** What every invariant clause raises about a position it is written about. */
    private static Set<Because> union(Set<Because> these, Set<Because> those) {
        Set<Because> out = new LinkedHashSet<>(these);
        out.addAll(those);
        return out;
    }

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
                Set<Owed> owed = bound.named().stream().map(Required::admittedValues)
                        .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
                owed.add(new Owed(CoverageObligation.BOUNDARY, bound.line()));
                yield new Some(owed);
            }
            // A clause about no position of this value raises no question about one. Not a rule
            // that went unread: what it says was read, and what it says is about nothing here.
            case ClauseStates.SomethingElse other -> other.positions().isEmpty()
                    ? new Irrelevant(Set.of(Because.IT_NAMES_NO_POSITION))
                    : new Some(other.positions().stream()
                            .map(Required::admittedValues).collect(java.util.stream.Collectors
                                    .toCollection(LinkedHashSet::new)));
            case ClauseStates.ARelation _ -> new Irrelevant(Set.of(Because.IT_RELATES_TWO_POSITIONS));
        };
    }

    /**
     * What a comparison written in a body or in an {@code ensures} raises about a position.
     *
     * <p>The invariant producer's counterpart, and the same classification underneath. What the
     * comparison places is {@link ComparisonClaim}'s and is read off the operator; whether there is
     * anything on the far side of the line is the construct's, and here there is — a body chooses
     * between the two sides and a clause holds a behavior to one, so both are values a row can
     * carry. An invariant refuses everything outside its bound at construction, which is why that
     * producer raises no {@link CoverageObligation#PARTITION} and this one does (ADR-0090).
     *
     * <p>Nothing a reading managed reaches this. What a comparison asks is settled by what it
     * places and what it places it about, both read off the comparison; what a reading made of it
     * is an answer, and is paired with these questions by {@link RuleAccounting#ofComparison}.
     *
     * @param claim what the comparison places, from the comparison alone
     * @param of    what it places it about, from the comparison alone as well
     */
    public static Required ofComparison(ComparisonClaim claim, ComparisonSubject of) {
        if (of instanceof ComparisonSubject.Relation between) {
            // An order between two things that move with the row is a line rows are owed at — the
            // place they hold one count — and divides neither of them, so there is no class of one
            // for a row to be owed in. Raised whether or not this compiler can find that place: a
            // question decided by a reading is what #851 is about, and `a <= b` and `a <= b + 1`
            // relate two positions alike (ADR-0090).
            //
            // An equality between them is not a line: it puts the whole of one arm on the place,
            // and that arm is a row the branch measure already asks for (`ComparedTerms`).
            return claim instanceof ComparisonClaim.Cut
                    ? new Some(new LinkedHashSet<>(java.util.List.of(
                            new Owed(CoverageObligation.BOUNDARY, between.at()))))
                    : new Irrelevant(Set.of(Because.IT_RELATES_TWO_POSITIONS));
        }
        if (!(of instanceof ComparisonSubject.AnInput input)) {
            return new Irrelevant(Set.of(Because.IT_NAMES_NO_POSITION));
        }
        Set<Owed> owed = new LinkedHashSet<>();
        switch (claim) {
            // An order across the place it names, so rows are owed either side of it and the two
            // sides have roles. A singling names the same place and has neither: the values on both
            // sides of it are one class. Both are about the number the comparison measures the
            // position by.
            case ComparisonClaim.Cut _ ->
                    owed.add(new Owed(CoverageObligation.BOUNDARY, input.place()));
            case ComparisonClaim.Singled _ ->
                    owed.add(new Owed(CoverageObligation.SINGLETON, input.place()));
            // Reached only by asking what an operator that compares nothing places. Every caller
            // walks comparisons; one arriving here has read something else as one.
            case ComparisonClaim.Nothing _ -> throw new IllegalArgumentException(
                    "a comparison that places nothing is not one this raises questions about");
        }
        // And the classes are the position's. A `String` bounded on its length draws its line on the
        // count and divides the strings, which is what {@link Owed} carries two subjects for.
        owed.add(new Owed(CoverageObligation.PARTITION, input.position()));
        return new Some(owed);
    }

    /**
     * What a comparison is written about, which the operator does not say.
     *
     * <p>The other half of what a comparison claims. {@code x == 10} singles a value out and
     * {@code x == y} says where one position stands against another, under one operator — so taken
     * from the operator alone, {@code a == b} raised a question about a value singled out at
     * {@code a} that no rule wrote.
     *
     * <p><b>Which of the two is decided by what moves with a row.</b> A comparison is about one
     * position exactly where one side is a number taken of an input and the other side is the same
     * for every row. Counted as positions named instead, {@code a <= a + 1} came back as one
     * position's — one name, twice — and a clause comparing an answer to an input needed a rule of
     * its own to be kept out. What a row chooses is the input; the answer moves with it, so a
     * comparison against the answer is a relation like any other.
     *
     * <p>Not read off what a reading managed. Whether this compiler could fold the other side is an
     * answer, and a question may not be decided by one (#851) — so {@code a == 10 * 2} is one
     * position's however unreadable the bound is.
     */
    public sealed interface ComparisonSubject {

        /**
         * One input, measured by the number on this side of the comparison.
         *
         * @param place    the number the comparison names, which is where a border or a singled
         *                 value falls
         * @param position the position it is a number of, which is what the classes are of
         */
        record AnInput(Owed.Subject place, Owed.Subject position) implements ComparisonSubject {

            public AnInput {
                if (place == null || position == null) {
                    throw new IllegalArgumentException("a comparison about an input names it");
                }
            }
        }

        /**
         * Both sides move with the row, so it is a rule about a pair.
         *
         * <p>Carries where the line it draws falls, which is on neither side: {@code r.a <= r.b + 1}
         * stops where the two hold one count. A marker alone would have left the question with
         * nowhere to be about; a subject picked from one side would name a place that rule never
         * stopped; and one written out would be as much of the place as this compiler can print.
         */
        record Relation(Owed.Subject.OfComparison at) implements ComparisonSubject {

            public Relation {
                if (at == null) {
                    throw new IllegalArgumentException("a rule about a pair is about both");
                }
            }
        }

        /** Neither side is an input's, so it says nothing about one. */
        record NoInput() implements ComparisonSubject {}
    }

    /**
     * What a reading of a body's or a declaration's comparison came to.
     *
     * <p>Three answers and not a line-or-nothing. A comparison this could not read as a line on one
     * position may still be one between two, and the second is a line rows are owed at while
     * dividing neither position — told apart here so that what it answers and what it leaves
     * standing are not the same set.
     */
    public sealed interface LineRead {

        /** A line on the position, which is where the classes either side of it come from. */
        record ALineOnThePosition() implements LineRead {}

        /** A line where two positions hold one count, which divides neither of them. */
        record ALineBetweenTwoPositions() implements LineRead {}

        /**
         * Neither, and what would have to change first.
         *
         * <p>In the words of the reading that turns a rule into a line, which is the same vocabulary
         * an invariant's own gives — a {@code guard}'s comparison and a newtype's bound are two
         * producers of one kind of evidence (spec §example-partition).
         */
        record NoLine(souther.compiler.inputs.BlockReason.AboutARule why) implements LineRead {

            public NoLine {
                if (why == null) {
                    throw new IllegalArgumentException("a reading that stopped says why");
                }
            }
        }
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
