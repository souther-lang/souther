package souther.compiler.numeric;

import java.math.BigDecimal;

/**
 * A number read as how many of something there are.
 *
 * <p>Not every number is one. A count is whole and no larger than the values there are to count, and
 * a number outside that names no quantity at all — so that question is asked here rather than at each
 * place that wants to build a collection of that many.
 *
 * <p>What is being counted is the caller's to know. A rule bounding {@code String.length} and one
 * bounding {@code List.length} reach the same reading, and the difference between characters and
 * elements is settled by the type the rule was written on.
 */
public final class CountDomain {

    /**
     * How many {@code min} says there are at least, or 0 where it says nothing about that.
     *
     * <p>One reading, because a floor is written on a type and on the record that has a value of it
     * as a field, and the two have to come to the same number from the same end. An end the range
     * stops short of is the next count up: a rule reading {@code > 3} is met by four and not by
     * three, and a caller reading the number and dropping whether the end is one of the range's own
     * has a floor one short of what was written.
     */
    public static int leastFrom(Endpoint min) {
        if (min == null) {
            return 0;
        }
        int at = asCount(min.at());
        if (at < 0) {
            return 0;
        }
        return min.inclusive() ? at : at + 1;
    }

    /**
     * The most a range reaching up to {@code max} allows, or every number where it reaches to no
     * end.
     *
     * <p>Beside {@link #leastFrom} and read from the same end rule: an end the range stops short of
     * is the count below it, so {@code < 3} allows two and not three. Written here rather than
     * beside each caller, because a cap and a floor that disagree about what an exclusive end means
     * refuse a value at one of them and offer it at the other.
     */
    public static int mostFrom(Endpoint max) {
        if (max == null) {
            return Integer.MAX_VALUE;
        }
        int at = asCount(max.at());
        if (at < 0) {
            return Integer.MAX_VALUE;
        }
        return max.inclusive() ? at : at - 1;
    }

    /** {@code at} as a number of things, or -1 where it is not one. */
    public static int asCount(Place at) {
        if (!(at instanceof Count count) || !count.whole()
                || count.at().compareTo(BigDecimal.valueOf(Integer.MAX_VALUE)) > 0
                || count.signum() < 0) {
            return -1;
        }
        return count.at().intValue();
    }

    private CountDomain() {}
}
