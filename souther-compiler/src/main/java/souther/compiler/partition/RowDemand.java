package souther.compiler.partition;

import souther.compiler.inputs.NameReach;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * What a row has to be for it to pass one condition, in the words a composer builds a row in.
 *
 * <p>A vocabulary of composing and not of conditions. Which operation an author wrote a condition
 * with, and which construct of the model it is, are the reading's; what is here is only what the
 * row is to hold, so two conditions written differently that ask the same of a row are one demand,
 * and a condition this compiler learns to read later lands in an arm here rather than growing a
 * kind of condition every composer has to know.
 *
 * <p>Asked of a condition met on the way and of a condition a run was seen coming out of alike —
 * the two places a row is held to something beside the classes it is composed for.
 */
public sealed interface RowDemand {

    /**
     * What a condition states of every row that passes it.
     *
     * <p>The demands a condition on the way can be read as. Held apart from a demand worked out from
     * one run, because a condition on the way says what every row reaching past it holds, and that
     * is what a region and a composer both narrow by.
     */
    sealed interface OfACondition extends RowDemand {

        /**
         * Every number of the input this asks something of.
         *
         * <p>Asked of the demand, for the reason {@link TakenConstraint#terms} is: what a composer
         * does first with a demand is find where each of its numbers is written, and read off the
         * shapes that act would be written once per shape.
         */
        Set<NumericTerm> terms();

        /**
         * Every position whose value this turns on.
         *
         * <p>Apart from {@link #terms}, which are the numbers among them. That an element is equal
         * to the value at another position turns on both and is no number of either, so a reader
         * asking whether a row still meets this after something of it moved asks these, and one
         * asking where a number is written asks the terms.
         */
        Set<TermPath> positions();

        /**
         * The positions among {@link #positions} whose value is only read: handed to a composer as
         * what something else is to hold or be kept from, and written nowhere by a row held to
         * this.
         *
         * <p>Apart from the rest because two readers ask two questions of the positions. Whether a
         * row still meets this after a step moved something turns on all of them; which parameters
         * holding a row to this composes is the rest — a set holding another parameter's value is
         * composed and that parameter is not.
         */
        Set<TermPath> valuesRead();
    }

    /**
     * What an element of a container is to meet.
     *
     * <p>Three vocabularies, because a composer meets them three ways. A relation over the
     * element's numbers, or the numbers beside it, or its own order is placed by a region, the way
     * every relation is. That the element — or a container inside it — holds the value at another
     * position is no relation a region carries — two strings differ by a distance on nothing — and
     * is met by writing that value into the container, or keeping it out. And a truth or a case of
     * a position inside it is a value written into the element.
     *
     * <p>A composer writes the elements of a container alike, so what is asked of one element is
     * written into each; two elements asked for two things are a row it does not write, and never
     * a row the model does not have.
     */
    sealed interface OfAnElement {

        /** Every position whose value this turns on, given the element it is asked of. */
        Set<TermPath> positions(TermPath element);

        /** The positions among those whose value is only read ({@link OfACondition#valuesRead}). */
        Set<TermPath> valuesRead();
    }

    /**
     * A relation over the row's numbers or over one position's own order.
     *
     * <p>Every condition a search narrows its region by is one of these. Which of the two
     * vocabularies the relation is spelled in is {@link TakenConstraint}'s answer, so a reader that
     * narrows a region asks this arm and nothing beside it.
     */
    record Relational(TakenConstraint constraint) implements OfACondition, OfAnElement {

        @Override
        public Set<NumericTerm> terms() {
            return constraint.terms();
        }

        @Override
        public Set<TermPath> positions() {
            Set<TermPath> out = new LinkedHashSet<>();
            constraint.terms().forEach(term -> out.add(term.subjectPath()));
            return Collections.unmodifiableSet(out);
        }

        @Override
        public Set<TermPath> positions(TermPath element) {
            return positions();
        }

        /** None: a row held to a relation writes every number it is over. */
        @Override
        public Set<TermPath> valuesRead() {
            return Set.of();
        }
    }

    /**
     * That the value at a {@code Bool} position is {@code held}.
     *
     * <p>A value to write and not a relation to place. A {@code Bool} is two values on no order, so
     * no region measures it and no carrier holds it; what passing the condition asks of a row is
     * which of the two stands there, and a composer meets that by writing it. So {@code a.flag},
     * {@code a.flag == true} and {@code a.flag /= false} coming out the way that gives them are
     * one demand, and the same three the other way round are the other.
     *
     * <p>Not a region's, so nothing narrowed by the way says a row past it holds this. What the way
     * asks in this vocabulary is {@link TruthsAsked}, which every composer handed the way writes
     * beside the numbers it places; two of these asking one position for both values are a way no
     * row takes ({@link Reachability.NothingReaches}).
     *
     * <p>Asked of an element as well, where the position is inside it: a composer writing the
     * elements of a container alike writes it into every one of them
     * ({@link ElementWrites}).
     *
     * @param at   the position the truth is read at
     * @param held which of the two values a row passing the condition holds there
     */
    record ATruth(TermPath at, boolean held) implements OfACondition, OfAnElement {

        public ATruth {
            Objects.requireNonNull(at, "the position a truth is read at");
        }

        /** None: a {@code Bool} is no number. */
        @Override
        public Set<NumericTerm> terms() {
            return Set.of();
        }

        @Override
        public Set<TermPath> positions() {
            return Set.of(at);
        }

        @Override
        public Set<TermPath> positions(TermPath element) {
            return positions();
        }

        /** None: a row held to this writes the value it asks for. */
        @Override
        public Set<TermPath> valuesRead() {
            return Set.of();
        }
    }

    /**
     * That the value at a position inside an element is one of the cases {@code position} is
     * narrowed to.
     *
     * <p>What a narrowing is on the way ({@link OnTheWay.Narrowed}), asked of an element. Not
     * carried as one: what a way narrows is what every row past it is, and this is what an element
     * is — so a composer writing the elements of a container alike writes every one of them as
     * one of these ({@link ElementWrites}), and two elements asked for two cases are two elements
     * and not a way no row takes.
     *
     * @param position  the narrowed position, the cases it is narrowed to written on it
     * @param crossings where the names the input's cases share are written, as a narrowing on the
     *                  way carries them
     */
    record InCases(TermPath position, List<NameReach.Crossing> crossings) implements OfAnElement {

        public InCases {
            if (position == null || !position.narrowsWhatItReaches()) {
                throw new IllegalArgumentException(
                        "a case of an element is a position read as one of its cases: " + position);
            }
            crossings = Requirements.of(position, crossings).crossings();
        }

        /** What has to hold of the parameter for the element to be one of these cases. */
        public Requirements requirements() {
            return Requirements.of(position, crossings);
        }

        @Override
        public Set<TermPath> positions(TermPath element) {
            return Set.of(position.narrowedFrom().position());
        }

        /** None: a row held to this writes the value it asks for. */
        @Override
        public Set<TermPath> valuesRead() {
            return Set.of();
        }
    }

    /**
     * That some element of the container at {@code container}, inside an element — or every
     * element of it, not {@code some} — is or is not another position's value.
     *
     * <p>What a quantifier over a container inside the element asks in the vocabulary that names
     * no position of the element ({@link SameAs}, {@link DifferentFrom}): the inner container is
     * named here, since what is that value is its element and not the outer one.
     *
     * @param container the container inside the element
     * @param some      whether some element of it is asked this, or every one
     * @param asked     what that element is asked: a {@link SameAs} or a {@link DifferentFrom}
     */
    record WithinIt(TermPath container, boolean some, OfAnElement asked) implements OfAnElement {

        public WithinIt {
            Objects.requireNonNull(container, "the container inside an element");
            if (!(asked instanceof SameAs) && !(asked instanceof DifferentFrom)) {
                throw new IllegalArgumentException("what names a position of the element names"
                        + " it already, and is asked of the element as it is: " + asked);
            }
        }

        @Override
        public Set<TermPath> positions(TermPath element) {
            Set<TermPath> out = new LinkedHashSet<>();
            out.add(container);
            out.addAll(asked.positions(container.element()));
            return Collections.unmodifiableSet(out);
        }

        @Override
        public Set<TermPath> valuesRead() {
            return asked.valuesRead();
        }
    }

    /**
     * That the element is equal to the value at {@code value}.
     *
     * <p>The element is not named here: it is always the element of the container the demand
     * holding this is about, and named twice the two could name different containers.
     */
    record SameAs(TermPath value) implements OfAnElement {

        public SameAs {
            Objects.requireNonNull(value, "the position whose value the element is");
        }

        @Override
        public Set<TermPath> positions(TermPath element) {
            return elementAndValue(element, value);
        }

        @Override
        public Set<TermPath> valuesRead() {
            return Set.of(value);
        }
    }

    /** That the element is unequal to the value at {@code value}. */
    record DifferentFrom(TermPath value) implements OfAnElement {

        public DifferentFrom {
            Objects.requireNonNull(value, "the position whose value the element is not");
        }

        @Override
        public Set<TermPath> positions(TermPath element) {
            return elementAndValue(element, value);
        }

        @Override
        public Set<TermPath> valuesRead() {
            return Set.of(value);
        }
    }

    /** {@code element} and then {@code value}, in that order whatever run it is. */
    private static Set<TermPath> elementAndValue(TermPath element, TermPath value) {
        Set<TermPath> out = new LinkedHashSet<>();
        out.add(element);
        out.add(value);
        return Collections.unmodifiableSet(out);
    }

    /** The relations among {@code asked}, which are what a region places. */
    static List<Relational> relationsAmong(List<OfAnElement> asked) {
        List<Relational> out = new ArrayList<>();
        for (OfAnElement each : asked) {
            if (each instanceof Relational relation) {
                out.add(relation);
            }
        }
        return List.copyOf(out);
    }

    /** The numbers {@code asked} is written with. */
    private static Set<NumericTerm> termsOf(List<OfAnElement> asked) {
        Set<NumericTerm> out = new LinkedHashSet<>();
        relationsAmong(asked).forEach(each -> out.addAll(each.terms()));
        return out;
    }

    /**
     * Every position a demand on the elements of {@code container} turns on: the container itself,
     * and what each of {@code asked} turns on beside it.
     *
     * <p>The container and not only its element. Which elements there are is the container's value,
     * so a step that moves how many it holds may take away the element that met what was asked,
     * or bring in one that does not — whatever it did to the element's own numbers.
     */
    private static Set<TermPath> positionsOf(TermPath container, List<OfAnElement> asked) {
        Set<TermPath> out = new LinkedHashSet<>();
        out.add(container);
        asked.forEach(each -> out.addAll(each.positions(container.element())));
        return out;
    }

    /** The positions {@code asked} only reads the value at. */
    private static Set<TermPath> valuesReadOf(List<OfAnElement> asked) {
        Set<TermPath> out = new LinkedHashSet<>();
        asked.forEach(each -> out.addAll(each.valuesRead()));
        return Collections.unmodifiableSet(out);
    }

    /**
     * That some element of a container meets every one of these.
     *
     * <p>Not a relation a region can be narrowed by. Each of them is stated of a term inside the
     * container's elements, and a region narrowed on one says every element meets it — which
     * excludes the rows where one element does and another does not, all of which pass. So what a
     * region is narrowed by is the container holding at least one, which every row past this does
     * hold, and what is done with the rest is compose: a row whose elements all meet them has one
     * that does.
     *
     * <p>The container's size is held here and not said beside this as a relation of its own.
     * Where the element is written the container is written holding it, so a row composed for the
     * element holds one already — and the size placed as a second number at the location the
     * element is written at is a second write of one value.
     *
     * <p>Where nothing an element can be meets them, no element does, which is what makes a cut
     * nothing can place here a proof the condition never comes out this way.
     *
     * <p>The container is held and not read back off the element's numbers. That the element is
     * another position's value is a demand with no number in it, and a container worked out from
     * the terms would be no container at all there.
     *
     * @param container   the container an element of which is to meet them
     * @param ofAnElement what the element is to meet, every one of it about the element and what
     *                    is inside it, and the numbers beside it a relation reads
     * @param holdingOne  the container's size at least one, which is a number of this input: a
     *                    container an element of which is asked something is a position, and
     *                    every type a container can be measures how many it holds
     */
    record Exists(TermPath container, List<OfAnElement> ofAnElement, Relational holdingOne)
            implements OfACondition {

        public Exists {
            Objects.requireNonNull(container, "a container an element of which meets them");
            Objects.requireNonNull(holdingOne, "the container holding one, which it does");
            ofAnElement = List.copyOf(ofAnElement);
            if (ofAnElement.isEmpty()) {
                throw new IllegalArgumentException(
                        "an element meeting nothing in particular is the container holding one");
            }
            // The value is written into the container as an element of its own, so what else is
            // asked of the element would be asked of another one: some element being `v` and
            // meeting `p` is not `v` written beside an element meeting `p`.
            if (ofAnElement.size() > 1
                    && ofAnElement.stream().anyMatch(each -> each instanceof SameAs)) {
                throw new IllegalArgumentException("an element that is another position's value"
                        + " is asked nothing beside it: " + ofAnElement);
            }
        }

        /** The relations among what the element is to meet. */
        public List<Relational> relations() {
            return relationsAmong(ofAnElement);
        }

        /** The numbers the element is written with, which are what a row composed for this
         *  places. */
        @Override
        public Set<NumericTerm> terms() {
            return Collections.unmodifiableSet(termsOf(ofAnElement));
        }

        @Override
        public Set<TermPath> positions() {
            return Collections.unmodifiableSet(positionsOf(container, ofAnElement));
        }

        @Override
        public Set<TermPath> valuesRead() {
            return valuesReadOf(ofAnElement);
        }
    }

    /**
     * That every element a container holds meets every one of these — which a container holding
     * none does.
     *
     * <p>Not a relation a region can be narrowed by, for the same reason {@link Exists} is not: a
     * term inside a container's elements is read by a region as the value of an element that is
     * there, and this says nothing about one being there. Narrowed on, a region would leave no
     * value where the rules leave the element none, and the way past an empty container would be
     * proved closed.
     *
     * <p>So what is done with these is compose, two ways round: elements that all meet them, and
     * where no element can be written that does, the container holding none.
     *
     * @param container     the container every element of which is to meet them
     * @param ofEachElement what every element is to meet, which may be about what stands beside
     *                      the element as much as about the element: a container holding none
     *                      meets all of it whatever that says
     * @param holdingNone   the container's size at most nought — the way to meet this with no
     *                      element at all, which is a number of this input as {@link Exists}'s is
     */
    record ForAll(TermPath container, List<OfAnElement> ofEachElement, Relational holdingNone)
            implements OfACondition {

        public ForAll {
            Objects.requireNonNull(container, "a container every element of which meets them");
            Objects.requireNonNull(holdingNone, "the container holding none, which it may");
            ofEachElement = List.copyOf(ofEachElement);
            if (ofEachElement.isEmpty()) {
                throw new IllegalArgumentException(
                        "every element meeting nothing in particular is no demand on a row");
            }
        }

        /** The relations among what every element is to meet. */
        public List<Relational> relations() {
            return relationsAmong(ofEachElement);
        }

        /** The numbers the element is written with and the container's size, which are what a
         *  row composed for this places — the first where it writes an element, the second where
         *  it writes none. */
        @Override
        public Set<NumericTerm> terms() {
            Set<NumericTerm> out = termsOf(ofEachElement);
            out.addAll(holdingNone.terms());
            return Collections.unmodifiableSet(out);
        }

        @Override
        public Set<TermPath> positions() {
            return Collections.unmodifiableSet(positionsOf(container, ofEachElement));
        }

        @Override
        public Set<TermPath> valuesRead() {
            return valuesReadOf(ofEachElement);
        }
    }

    /**
     * That so many elements of a container meet a statement: the count against a number.
     *
     * <p>Not a relation a region can be narrowed by, for the reason {@link Exists} is not, and more:
     * the count is no number of the row at all. What is done with this is compose — a container
     * with as many elements meeting the statement as this leaves it, written together with every
     * other count of that container a row is asked for ({@link CardinalityComposer}).
     *
     * @param count             what is counted: the container, and what an element is counted
     *                          for meeting
     * @param met               how the count stands to {@code level} on every row this holds of
     * @param level             the number the count, with {@code against} added to it, is held
     *                          against
     * @param against           what a form of the input's numbers comes to, added to the count
     *                          before it is held against {@code level}; no coefficient where the
     *                          count is held against a number alone
     * @param anElementMeeting  what an element meeting what is counted is held to, as relations,
     *                          where it is that ({@link DemandReading#anElementMeeting})
     */
    record SoMany(Quantity.HowManyMeet count, Rel met, ExactRatio level,
                  LinearForm<NumericTerm> against,
                  Optional<List<TakenConstraint>> anElementMeeting)
            implements OfACondition {

        public SoMany {
            Objects.requireNonNull(count, "a count of the elements of some container");
            Objects.requireNonNull(met, "a count held against a number some way");
            Objects.requireNonNull(level, "a count held against some number");
            Objects.requireNonNull(against, "what is added to the count, or nothing");
            Objects.requireNonNull(anElementMeeting,
                    "what an element meeting it is held to is said, or said to be nothing read");
            if (against.constant().signum() != 0) {
                throw new IllegalArgumentException(
                        "what is added to the count has no constant; it is in the level: " + against);
            }
        }

        /** Whether the count is held against numbers of the input, which stand where the row puts
         *  them, and not against a number alone. */
        public boolean againstNumbers() {
            return !against.coefs().isEmpty();
        }

        /**
         * The counts this leaves, as what a count a row is composed at is one of.
         *
         * <p>A region and not one of its counts. Several conditions on one count are met where
         * their regions cross, and which count of that a container is composed at is the
         * composing's to choose.
         *
         * <p>Of a count held against a number alone. Where numbers of the input are added to it the
         * counts it leaves are those of where the row puts them ({@link #countsWhere}).
         */
        public NumbersAskedFor counts() {
            if (againstNumbers()) {
                throw new IllegalStateException("the counts this leaves are those of where the"
                        + " numbers added to it stand: " + this);
            }
            return NumbersAskedFor.of(regionOf(level));
        }

        /**
         * The counts this leaves where the numbers added to it come to {@code added}, or null where
         * the level less that is a number no exact ratio holds.
         */
        public LevelRegion countsWhere(ExactRatio added) {
            return level.minus(added) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio at)
                    ? regionOf(at) : null;
        }

        private LevelRegion regionOf(ExactRatio threshold) {
            Level at = new Level.OfTheQuantity(threshold);
            return switch (met) {
                case EQ -> LevelRegion.point(at);
                case NE -> LevelRegion.EVERYTHING.without(at);
                case GE -> LevelRegion.of(new LevelInterval(Bound.at(at, true), null));
                case GT -> LevelRegion.of(new LevelInterval(Bound.at(at, false), null));
                case LE -> LevelRegion.of(new LevelInterval(null, Bound.at(at, true)));
                case LT -> LevelRegion.of(new LevelInterval(null, Bound.at(at, false)));
            };
        }

        /** The numbers the statement reads, of the elements and beside them, and the numbers added
         *  to the count. */
        @Override
        public Set<NumericTerm> terms() {
            Set<NumericTerm> out = new LinkedHashSet<>(AStatementAtARow.numbersOf(
                    count.ofTheElement()));
            out.addAll(against.coefs().keySet());
            return Collections.unmodifiableSet(out);
        }

        @Override
        public Set<TermPath> positions() {
            Set<TermPath> out = new LinkedHashSet<>();
            out.add(count.container());
            terms().forEach(term -> out.add(term.subjectPath()));
            return Collections.unmodifiableSet(out);
        }

        /** None: a row held to this writes the container and whatever the statement reads beside
         *  an element. */
        @Override
        public Set<TermPath> valuesRead() {
            return Set.of();
        }
    }

    /**
     * A statement read to the end that no composer writes a row toward, which the run of a row
     * says whether it held.
     *
     * <p>Asked of a row all the same: a row past the condition is one whose run comes out this way,
     * whatever it took to compose it. What is missing is a composer for {@code why}, which is a
     * limit of composing and not of what the condition says — so nothing is placed for it, and the
     * row is put to the run ({@link ReachabilityGap.Why.NoComposerWritesIt}).
     *
     * <p>A value the body works out is no number of the input because the reading of what it was
     * made from stopped somewhere ({@link Quantity.OfABinding#madeOf}), and that is what a row
     * would have to be composed past: it travels with this, so what is said of the row says where.
     *
     * @param statement what the condition states, coming out the way the row is to
     * @param why       which kind of statement no composer writes toward
     * @param past      where the reading of what the values it is over were made from stopped,
     *                  each once; empty where nothing of them was read to stop
     */
    record ForTheRun(Proposition statement, NoComposer why, List<WhyUnread> past)
            implements OfACondition {

        public ForTheRun {
            Objects.requireNonNull(statement, "a statement about some value");
            Objects.requireNonNull(why, "a statement no composer writes is of some kind");
            past = List.copyOf(new LinkedHashSet<>(past));
        }

        /** None: a composer places nothing for this, and the run says whether it held. */
        @Override
        public Set<NumericTerm> terms() {
            return Set.of();
        }

        @Override
        public Set<TermPath> positions() {
            return Set.of();
        }

        @Override
        public Set<TermPath> valuesRead() {
            return Set.of();
        }
    }

    /**
     * Which kind of statement read to the end no composer writes a row toward.
     *
     * <p>Each is what composing reaches and not what a condition says: the statement was read and
     * is asked of a row, and the composer that would write a row meeting it is the part missing.
     */
    enum NoComposer {

        /** A relation over a number the body works out, which no position of a row holds. */
        A_VALUE_THE_BODY_WORKS_OUT,

        /** How many elements of a container meet something, where no container is composed to the
         *  count: held against more than one number, or counted for what no element is composed
         *  to meet. */
        A_COUNT_OF_ELEMENTS,

        /** How many elements of a container meet something, held against a number no exact
         *  ratio holds. */
        A_COUNT_AGAINST_A_NUMBER_NOT_HELD,

        /** How many elements of a container inside an element of another meet something. */
        A_COUNT_WITHIN_AN_ELEMENT,

        /** How many different values the elements of a container come to, or what a number of
         *  each adds up to over them. */
        A_NUMBER_OVER_ELEMENTS,

        /** What a division by a written number leaves of a form of several numbers, which no
         *  position holds and no composer writes a row at when it is what a way passes. */
        A_REMAINDER_OF_A_FORM,

        /** Two subjects of a row being one value. */
        TWO_SUBJECTS_ONE_VALUE,

        /** A place on an order, of a term that is no one position. */
        AN_ORDER_OF_NO_ONE_POSITION
    }

    /**
     * Where the terms of one comparison stand, at a point of its border on the side it comes out
     * on.
     *
     * <p>Not a condition, and so not something a way can take in. A point is what a search found
     * for one comparison, and it says more than the comparison does: every row past the comparison
     * holds its relation, and a row held to this stands at one place of it. What a border's own
     * search composes first is a point, and a row held to this is held to the same demand a row at
     * the point is.
     *
     * <p>Demands and not assignments, in the vocabulary a point of a border is composed in: where
     * each term the comparison reads has to stand ({@link Realization.Found#fixing}) and every
     * number it may take there. So a term no position holds on its own — the sum of what a list's
     * elements hold — is a demand on whatever writes the list, and the elements are composed to
     * meet it.
     *
     * @param fixing where the terms of the comparison stand, at a place on the side it comes out on
     * @param asking every number each of those terms may take and still be on that side
     */
    record AtAPoint(Map<RealizationTarget, Place> fixing, NumbersAskedFor asking)
            implements RowDemand {

        public AtAPoint {
            // In the order the search fixed them, which a reader walking the demands meets them in.
            fixing = Collections.unmodifiableMap(new LinkedHashMap<>(fixing));
            if (fixing.isEmpty()) {
                throw new IllegalArgumentException("a point is a term standing somewhere");
            }
        }
    }
}
