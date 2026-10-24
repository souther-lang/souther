package souther.compiler.partition;

import java.util.Comparator;
import java.util.PriorityQueue;

/**
 * The order the alternatives of choices are looked for ways in, where the ways that can be handed
 * on are fewer than the alternatives: the alternative with the smaller number first, and among
 * those of one number the choice that was met first.
 *
 * <p>So that no alternative is passed over for a later one of another choice, and what a figure
 * leaves out is the later alternatives of whichever choice has the most. This is the one place
 * that says it. The walk over the conditions of a way, the ways its groups come to together, and
 * the parts of a row's demand each ask this rather than keep an order of their own: an order kept
 * where it is used is the order that goes unstated in the next place that needs one.
 *
 * <p>A choice can be met after others have been asked about: the choice an alternative holds is
 * met only when that alternative is looked at. It joins the order at its place, and the numbers
 * that have been passed over for the others are not passed over for it — its second alternative
 * comes before the third of every choice already met.
 *
 * @param <K> what stands for a choice. Two choices that are equal are two choices, so this orders
 *            them by when each was met and never asks whether two keys are equal
 */
final class AlternativeOrder<K> {

    /** One alternative of one choice. */
    record Target<K>(K choice, int alternative) {}

    private record Queued<K>(K choice, int alternative, int met) {}

    private final PriorityQueue<Queued<K>> owed = new PriorityQueue<>(
            Comparator.<Queued<K>>comparingInt(Queued::alternative)
                    .thenComparingInt(Queued::met));

    private int metSoFar;

    /** A choice with {@code alternatives} alternatives, met now: every one of them is owed. */
    void met(K choice, int alternatives) {
        int order = metSoFar++;
        for (int each = 0; each < alternatives; each++) {
            owed.add(new Queued<>(choice, each, order));
        }
    }

    /** The alternative owed next, or null where none is. */
    Target<K> next() {
        Queued<K> first = owed.poll();
        return first == null ? null : new Target<>(first.choice(), first.alternative());
    }
}
