package souther.compiler.check;

import java.util.List;
import java.util.Objects;

/**
 * The comparisons one flat condition states, in their reading order, each with how much of the
 * condition it is.
 *
 * <p>A condition can state more than one. {@code Int.compare(a, b) >= 0} states a bound on the sign
 * that operation answers, and it states the order of the two values that sign is the order of.
 * Which of them a reader can do anything with is not known until it is read — a date this check can
 * name is one thing, and the date a day after it is another — so all of them are handed over and
 * the choosing is the reader's.
 *
 * <p><b>Not every reading is the condition.</b> {@code Int.compare(a, b) >= 0} is {@code a >= b}
 * exactly, but {@code Date.daysBetween(a, b) > 1} only proves {@code b > a}: a day apart, the order
 * holds and the condition does not. A reading that only follows from the condition holds where the
 * condition holds and says nothing where it fails, and owing it is owing less than the condition. So
 * the readings are not handed over as one list a reader then takes under either polarity: a reader
 * asks for the ones that hold where the condition comes out one way ({@link #holdingWhere}), or for
 * the ones that are the condition ({@link #theCondition}), and a reading that only follows from it
 * is never one it can turn round.
 *
 * <p><b>The order is a reading order.</b> A comparison derived from another comes before the one it
 * was derived from, so repeated composition puts the deepest reading first and the comparison as
 * written last. That is not a ranking: the two are about different values. Which one a reader takes
 * is its own, and each of them says so in one line — a clause takes the first it can read, a guard
 * takes every one.
 */
final class ComparisonReadings {

    /**
     * One comparison a condition states.
     *
     * @param stated        what it compares, and the claim it places, where the condition holds
     * @param isTheCondition whether it holds exactly where the condition does, and not only
     *                      wherever the condition does
     */
    record Reading(StatedComparison stated, boolean isTheCondition) {

        Reading {
            Objects.requireNonNull(stated, "a reading states a comparison");
        }
    }

    private final List<Reading> inReadingOrder;

    ComparisonReadings(List<Reading> inReadingOrder) {
        this.inReadingOrder = List.copyOf(inReadingOrder);
    }

    /** Nothing states a comparison here, which is every condition that is not one. */
    static ComparisonReadings none() {
        return new ComparisonReadings(List.of());
    }

    /**
     * The comparisons that hold where the condition comes out {@code positive}, in reading order.
     *
     * <p>Every reading where it holds; where it fails, only the ones that are the condition, since
     * the failure of a condition is no failure of what it only proves. Each is still the comparison
     * as it stands where the condition holds, and the caller states it under {@code positive}.
     */
    List<StatedComparison> holdingWhere(boolean positive) {
        return inReadingOrder.stream()
                .filter(reading -> positive || reading.isTheCondition())
                .map(Reading::stated)
                .toList();
    }

    /**
     * The comparisons that are the condition, in reading order: what owing it owes, whichever way
     * round it is owed.
     *
     * <p>Not what it only proves. Established, that would discharge a clause that asks more, and a
     * clause taking the first reading it can read would take the weaker one in place of itself.
     */
    List<StatedComparison> theCondition() {
        return inReadingOrder.stream()
                .filter(Reading::isTheCondition)
                .map(Reading::stated)
                .toList();
    }
}
