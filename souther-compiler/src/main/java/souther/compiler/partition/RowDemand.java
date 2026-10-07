package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Place;

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
     * What an element of a container is to meet, about the element and nothing beside it but the
     * values it is compared with.
     *
     * <p>Two vocabularies, because a composer meets them two ways. A relation over the element's
     * numbers or its own order is placed by a region, the way every relation is; that the element
     * is the value at another position is no relation a region carries — two strings differ by a
     * distance on nothing — and is met by writing that value into the container, or keeping it out.
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
     * @param at   the position the truth is read at
     * @param held which of the two values a row passing the condition holds there
     */
    record ATruth(TermPath at, boolean held) implements OfACondition {

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

        /** None: a row held to this writes the value it asks for. */
        @Override
        public Set<TermPath> valuesRead() {
            return Set.of();
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
     * @param ofAnElement what the element is to meet, every one of it about the element alone
     * @param holdingOne  the container's size at least one, where the size is a number of this
     *                    input a region can carry
     */
    record Exists(TermPath container, List<OfAnElement> ofAnElement,
                  Optional<Relational> holdingOne)
            implements OfACondition {

        public Exists {
            Objects.requireNonNull(container, "a container an element of which meets them");
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
     * @param ofEachElement what every element is to meet, every one of it about the element alone
     * @param holdingNone   the container's size at most nought, where the size is a number of this
     *                      input a region can carry — the way to meet this with no element at all
     */
    record ForAll(TermPath container, List<OfAnElement> ofEachElement,
                  Optional<Relational> holdingNone)
            implements OfACondition {

        public ForAll {
            Objects.requireNonNull(container, "a container every element of which meets them");
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
            holdingNone.ifPresent(none -> out.addAll(none.terms()));
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
