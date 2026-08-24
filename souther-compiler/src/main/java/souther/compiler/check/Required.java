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
        IT_NAMES_NO_POSITION,

        /**
         * The rule reads what the behavior answers, and this reading does not project such a rule
         * back onto the input space.
         *
         * <p>Told from {@link #IT_NAMES_NO_POSITION}, which is the reason a reader would otherwise
         * be given. {@code List.length(value.articles) <= query.limit.value} does name a position —
         * a row chooses {@code query.limit} — and what it raises nothing about is the input's own
         * values, because what the clause bounds is on the other side of the behavior. An author
         * told the rule names no position would go looking for the name that is plainly there.
         */
        IT_DEPENDS_ON_THE_ANSWER,

        /**
         * The rule singles a value out on a quantity that is a form over several positions, which
         * singles one out of none of them.
         *
         * <p>{@code a == b} puts the whole of one arm on the place the two meet, and
         * {@code a + b == 10} the whole of one arm on the place their sum reaches ten. Either way
         * that arm is a row the branch measure already asks for. Not every rule over such a form:
         * an order across one draws a line, and that is a question raised rather than one nobody
         * has.
         */
        IT_SINGLES_ACROSS_POSITIONS,

        /**
         * The rule was read to the end and the quantity it cuts is nothing.
         *
         * <p>Told from {@link #IT_NAMES_NO_POSITION}, which says the rule mentions nowhere, and
         * from {@link #IT_WAS_NOT_READ}, which says this compiler fell short. {@code a <= a}
         * mentions a position, was read in full, and holds of every row.
         */
        IT_CUTS_NOTHING,

        /**
         * The rule cuts a quantity somewhere the quantity never reaches.
         *
         * <p>Three times a length is never negative, so a rule comparing one against a negative
         * draws no border and divides the position into nothing. Understood rather than unread,
         * which is why it is not {@link #IT_WAS_NOT_READ}.
         */
        IT_CUTS_WHERE_THE_QUANTITY_DOES_NOT_RUN,

        /**
         * The rule names a value on the quantity that the quantity does not hold.
         *
         * <p>{@code 2 * a == 9} takes the even numbers and nine is not one of them, so no whole
         * number is put in a class of its own. The rule was read and what it says is that no row
         * satisfies it.
         */
        IT_NAMES_NO_VALUE_THE_QUANTITY_HOLDS,

        /**
         * Nothing here turned the rule into a line, so what it raises is not known.
         *
         * <p>Which is why nothing is raised rather than the questions a line would raise. What such
         * a rule divides, and into how many classes, is the part that was not read.
         */
        IT_WAS_NOT_READ
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
    public static Required ofComparison(ComparisonSubject of) {
        // One switch and no `default`, for the reason {@link #ofInvariant} gives: a subject added
        // and not classified stops the build rather than arriving here as the arm that happens to be
        // nearest. Written as a chain ending in "anything that is not an input", the arm for a
        // comparison reading the answer could have been left out and every such comparison would
        // have been reported as naming no position — the reason a reader is given, quietly wrong.
        return switch (of) {
            // A rule this reading does not put on the input space at all. Before anything about the
            // two sides, because a comparison reading the answer is not a pair of inputs however
            // its sides are spelled: read as one, an order against the answer raised the line a pair
            // of inputs raises and nothing could ever answer it.
            case ComparisonSubject.AnswerDependent _ ->
                    new Irrelevant(Set.of(Because.IT_DEPENDS_ON_THE_ANSWER));
            // A line on a quantity that is no position's own values is one rows are owed at — the
            // place the positions of the form hold the count the rule wrote — and divides none of
            // them, so there is no class of one for a row to be owed in.
            //
            // A value singled out on such a quantity is not a line: it puts the whole of one arm on
            // the place, and that arm is a row the branch measure already asks for.
            case ComparisonSubject.AcrossPositions between ->
                    between.places() == Places.ACROSS_THE_VALUE
                            ? new Some(new LinkedHashSet<>(java.util.List.of(
                                    new Owed(CoverageObligation.BOUNDARY, between.at()))))
                            : new Irrelevant(Set.of(Because.IT_SINGLES_ACROSS_POSITIONS));
            case ComparisonSubject.NoInput _ ->
                    new Irrelevant(Set.of(Because.IT_NAMES_NO_POSITION));
            case ComparisonSubject.CutsNothing _ ->
                    new Irrelevant(Set.of(Because.IT_CUTS_NOTHING));
            case ComparisonSubject.OutsideTheDomain _ ->
                    new Irrelevant(Set.of(Because.IT_CUTS_WHERE_THE_QUANTITY_DOES_NOT_RUN));
            case ComparisonSubject.Unread _ ->
                    new Irrelevant(Set.of(Because.IT_WAS_NOT_READ));
            case ComparisonSubject.AnInput input -> ofAnInput(input);
        };
    }

    /** What a comparison measuring one input by a number of it raises about that input. */
    private static Required ofAnInput(ComparisonSubject.AnInput input) {
        Set<Owed> owed = new LinkedHashSet<>();
        switch (input.places()) {
            // An order across the place it names, so rows are owed either side of it and the two
            // sides have roles. A singling names the same place and has neither: the values on both
            // sides of it are one class. Both are about the number the comparison measures the
            // position by.
            case ACROSS_THE_VALUE -> owed.add(new Owed(CoverageObligation.BOUNDARY, input.place()));
            case AT_THE_VALUE -> owed.add(new Owed(CoverageObligation.SINGLETON, input.place()));
            // A value the quantity does not hold: `2 * a == 9` divides the whole numbers nowhere,
            // because there is no whole number the rule names. The position is not divided and no
            // row can be written at the place, so neither question has anything to be about.
            case AT_NO_VALUE -> {
                return new Irrelevant(Set.of(Because.IT_NAMES_NO_VALUE_THE_QUANTITY_HOLDS));
            }
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
     * <p><b>Which of them it is, is decided by what the two sides read.</b> A comparison is about
     * one position exactly where one side is a number taken of an input and the other side is the
     * same for every row. Counted as positions named instead, {@code a <= a + 1} came back as one
     * position's — one name, twice.
     *
     * <p><b>And a comparison reading the answer is none of the three.</b> The answer does move with
     * the row, which is what a clause of an {@code ensures} is written about; what does not follow
     * is that two things moving with the row are one kind of subject here. Boundary coverage is over
     * the values a row can choose, and those are the inputs — so an order between two inputs is a
     * line rows are owed at, and an order between an input and the answer is not a line on the input
     * space at all. Read as one, {@code List.length(value.articles) <= query.limit.value} raised a
     * boundary obligation at a place no reading of the clause can reach (issue #1013).
     *
     * <p>Not read off what a reading managed. Whether this compiler could fold the other side is an
     * answer, and a question may not be decided by one (#851) — so {@code a == 10 * 2} is one
     * position's however unreadable the bound is.
     */
    public sealed interface ComparisonSubject {

        /**
         * One input, measured by the number the canonical quantity is that position's own values
         * of.
         *
         * @param place    the number the rule cuts the position at, which is where a border or a
         *                 singled value falls. The quantity's own, so a rule that wrote a multiple
         *                 of the position names it where the position holds it
         * @param position the position it is a number of, which is what the classes are of
         * @param places   what the comparison does to that number
         */
        record AnInput(Owed.Subject place, Owed.Subject position, Places places)
                implements ComparisonSubject {

            public AnInput {
                if (place == null || position == null || places == null) {
                    throw new IllegalArgumentException("a comparison about an input names it");
                }
            }
        }

        /**
         * The quantity the rule cuts is a form over more than one position, so the line is on none
         * of them.
         *
         * <p>Carries where the line falls, which is on no position: {@code r.a <= r.b + 1} stops
         * where the two hold one count, and {@code a + b <= 10} where their sum reaches ten. A
         * marker alone would have left the question with nowhere to be about; a subject picked from
         * one position would name a place that rule never stopped; and one written out would be as
         * much of the place as this compiler can print.
         *
         * <p>A distance and a general form together, because coverage asks one thing of both: no
         * position is divided, and the place is the comparison's to name. Which of the two shapes
         * the quantity is, is a fact about the quantity and is carried where quantities are.
         */
        record AcrossPositions(Owed.Subject.OfComparison at, Places places)
                implements ComparisonSubject {

            public AcrossPositions {
                if (at == null || places == null) {
                    throw new IllegalArgumentException("a rule over a form is about the form");
                }
            }
        }

        /**
         * The comparison reads what the behavior answers, so this reading does not put it on the
         * input space.
         *
         * <p>Apart from {@link NoInput}, which the shape used to fall into where the other side was
         * a constant, and apart from {@link AcrossPositions}, which it fell into where the other
         * side was an input. Both were silent about a different thing than this is: one says the
         * rule names no input, and {@code List.length(value.articles) <= query.limit.value} names
         * one.
         *
         * <p>Not a claim that no line exists. Eliminating the answer existentially can leave a
         * constraint on the input — a length is never negative, so {@code List.length(value.items)
         * <= n} has no satisfying answer below zero — and deriving that is constraint projection
         * over several rules rather than the reading of one comparison. What this arm records is
         * where the reading stops, so that adding the projection later contradicts nothing.
         */
        record AnswerDependent() implements ComparisonSubject {}

        /**
         * Neither side is an input's, so it says nothing about one.
         *
         * <p>{@code 20 <= 30} is one. Apart from {@link CutsNothing}, which names positions and
         * cancels them, and apart from {@link Unread}, which names one this compiler could not
         * read: all three raise nothing, and a reader told the wrong one goes looking for something
         * that is not there.
         */
        record NoInput() implements ComparisonSubject {}

        /**
         * The comparison was read to the end and the quantity it cuts is nothing.
         *
         * <p>{@code a <= a} and {@code a - a <= 0} name a position, and what they say about it is
         * that every row satisfies them. Nothing is missing here and no reading fell short, which
         * is what tells this from {@link Unread}: read as one, a tautology owed a row at a place it
         * never stopped, and nothing could ever be written there.
         */
        record CutsNothing() implements ComparisonSubject {}

        /**
         * The comparison was read, the quantity and the line are both known, and the quantity does
         * not run as far as the line.
         *
         * <p>A length is never negative, so {@code List.length(xs) <= -1} draws no border: there is
         * no value either side for a row to be owed at, and no class the position is divided into.
         * Read as a line this compiler could not take in, an author was sent after a limit that is
         * not there; read as a line, a row was owed where the model has nothing.
         */
        record OutsideTheDomain() implements ComparisonSubject {}

        /**
         * The comparison names a position and nothing here turned it into a line.
         *
         * <p>In the words of the reading that turns a rule into a line, which is the same vocabulary
         * an invariant's own gives — a {@code guard}'s comparison and a newtype's bound are two
         * producers of one kind of evidence (spec §example-partition).
         *
         * <p>Raising nothing rather than raising the questions a line would have raised. What a
         * comparison this could not read divides, and into how many classes, is exactly what is not
         * known: {@code a * a <= 9} cuts the whole numbers twice, and the positions the walk names
         * for filing include ones the arithmetic would have cancelled. An obligation built from
         * those would be the operands read as written, one arm along.
         */
        record Unread(souther.compiler.inputs.BlockReason.AboutARule why)
                implements ComparisonSubject {

            public Unread {
                if (why == null) {
                    throw new IllegalArgumentException("a reading that stopped says why");
                }
            }
        }
    }

    /**
     * What a comparison does to the quantity it cuts.
     *
     * <p>Read off the canonical quantity together with the operator, and read once. The operator
     * alone does not answer it: {@code 2 * a == 8} names four and {@code 2 * a == 9} names no whole
     * number at all, under one operator and one shape of rule.
     */
    public enum Places {

        /** An order across the line, so rows are owed either side of it and the two sides have
         *  roles. */
        ACROSS_THE_VALUE,

        /** One value put in a class of its own, which has no sides: the values either side of it
         *  are one class. */
        AT_THE_VALUE,

        /** A value the quantity does not hold, which puts nothing in a class of its own. */
        AT_NO_VALUE
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
