package souther.compiler.partition;

import souther.compiler.numeric.Place;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

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
    sealed interface OfACondition extends RowDemand {}

    /**
     * A relation over the row's numbers or over one position's own order.
     *
     * <p>Every condition a search narrows its region by is one of these. Which of the two
     * vocabularies the relation is spelled in is {@link TakenConstraint}'s answer, so a reader that
     * narrows a region asks this arm and nothing beside it.
     */
    record Relational(TakenConstraint constraint) implements OfACondition {}

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
