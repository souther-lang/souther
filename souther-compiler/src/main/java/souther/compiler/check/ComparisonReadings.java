package souther.compiler.check;

import java.util.List;

/**
 * The comparisons one flat condition states, in their reading order.
 *
 * <p>A condition can state more than one. {@code Int.compare(a, b) >= 0} states a bound on the sign
 * that operation answers, and it states the order of the two values that sign is the order of, and
 * both hold of the same values. Which of them a reader can do anything with is not known until it is
 * read — a date this check can name is one thing, and the date a day after it is another — so all of
 * them are handed over and the choosing is the reader's.
 *
 * <p><b>The order is what this type knows, and it is the only thing it knows about them.</b> A
 * comparison derived from another comes before the one it was derived from, so repeated composition
 * puts the deepest reading first and the comparison as written last. That is a reading order and not
 * a ranking: the two are about different values, and neither of them says more than the other.
 * Which one a reader takes is its own, and each of them says so in one line — a clause takes the
 * first it can read, a guard takes every one.
 *
 * <p>Nothing here says which of them the source wrote. Nobody asks: a report about a clause anchors
 * on the expression the caller was handed, and a reader that wanted the distinction would be asking
 * about how the readings were made rather than about what they state.
 */
record ComparisonReadings(List<StatedComparison> inReadingOrder) {

    /** Fixed here, because the order is the whole of what this states. */
    ComparisonReadings {
        inReadingOrder = List.copyOf(inReadingOrder);
    }

    /** Nothing states a comparison here, which is every condition that is not one. */
    static ComparisonReadings none() {
        return new ComparisonReadings(List.of());
    }
}
