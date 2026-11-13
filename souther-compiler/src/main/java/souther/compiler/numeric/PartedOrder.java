package souther.compiler.numeric;

import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

/**
 * An order that compares two positions of one part by the places that part's question was stated
 * with, and any other two by the order itself.
 *
 * <p>The closure of each part is asked with the places of the positions the part weighs, worked out
 * once for the part ({@link ClosureQuestion#places}), so two positions of one part are compared by
 * two numbers that were already there. A comparison of two positions can be dear — it reads the
 * structure of two terms — and a form is walked once for every question put to it, so a form over a
 * run of positions of one part, and one more of another, is put in order by as many dear
 * comparisons as that one position is compared with.
 *
 * <p>It is the same order as the one it is made over: for every pair it says what that says, which
 * is what the places were worked out to. So nothing about a walk changes but what it costs — what
 * is walked first, and which pairs the walk refuses, are {@link CanonicalOrder#walking}'s, which
 * this does not repeat. And it holds the places of no positions of its own and works none out: it
 * is handed the parts and what each was asked with, and reads them, so what outlives it is nothing
 * beyond what the closure of the parts holds.
 *
 * @param <A> what a position is
 */
final class PartedOrder<A> implements CanonicalOrder<A> {

    /** Which part weighs each position. */
    private final Map<A, Integer> partOf;

    /** The question each part put, which holds the places of the positions it weighs. */
    private final List<ClosureQuestion<A>> questions;

    private final CanonicalOrder<A> order;

    PartedOrder(Map<A, Integer> partOf, List<ClosureQuestion<A>> questions,
                CanonicalOrder<A> order) {
        this.partOf = partOf;
        this.questions = questions;
        this.order = order;
    }

    @Override
    public int compare(A one, A other) {
        Integer part = partOf.get(one);
        if (part != null && part.equals(partOf.get(other))) {
            Map<A, Integer> places = questions.get(part).places();
            Integer placeOfOne = places.get(one);
            Integer placeOfOther = places.get(other);
            if (placeOfOne != null && placeOfOther != null) {
                return Integer.compare(placeOfOne, placeOfOther);
            }
        }
        return order.compare(one, other);
    }

    @Override
    public List<Map.Entry<A, ExactRatio>> walkOf(CanonicalForm<A> form,
                                                 Supplier<List<Map.Entry<A, ExactRatio>>> walk) {
        return order.walkOf(form, walk);
    }
}
