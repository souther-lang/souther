package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
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
    }

    /**
     * A relation over the row's numbers or over one position's own order.
     *
     * <p>Every condition a search narrows its region by is one of these. Which of the two
     * vocabularies the relation is spelled in is {@link TakenConstraint}'s answer, so a reader that
     * narrows a region asks this arm and nothing beside it.
     */
    record Relational(TakenConstraint constraint) implements OfACondition {

        @Override
        public Set<NumericTerm> terms() {
            return constraint.terms();
        }
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
     * @param ofAnElement what the element is to meet, every one of it about the element alone
     * @param holdingOne  the container's size at least one, where the size is a number of this
     *                    input a region can carry
     */
    record Exists(List<Relational> ofAnElement, Optional<Relational> holdingOne)
            implements OfACondition {

        public Exists {
            ofAnElement = List.copyOf(ofAnElement);
            if (ofAnElement.isEmpty()) {
                throw new IllegalArgumentException(
                        "an element meeting nothing in particular is the container holding one");
            }
        }

        /** The numbers the element is written with, which are what a row composed for this
         *  places. */
        @Override
        public Set<NumericTerm> terms() {
            Set<NumericTerm> out = new LinkedHashSet<>();
            ofAnElement.forEach(each -> out.addAll(each.terms()));
            return Collections.unmodifiableSet(out);
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
