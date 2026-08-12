package souther.compiler.numeric;

/**
 * How many values a type has at most, or that no such number was proven.
 *
 * <p>An upper bound and never an exact count. What it is for is deciding that something cannot be
 * filled — a set of two needs two values of its element that differ — and for that the answer has to
 * be wide wherever the reading fell short. {@link #UNKNOWN} is that wide answer: not a large number,
 * but no number at all, and every question asked of it comes back the way that refuses nothing.
 *
 * <p>{@link #NO_VALUE} is the other end and is a claim rather than an absence. A type is only said to
 * have none where the rules that reach it leave none, so the arithmetic here must never arrive at it
 * by dropping something it could not read.
 *
 * <p>The product is where the two ends meet. A record is the product of what its fields hold, and a
 * field with no value leaves the record none however wide the field beside it is — so
 * {@code NO_VALUE × UNKNOWN} is {@code NO_VALUE}, which is not what an unknown-swallows-everything
 * reading gives. The sum is the ordinary one: an unknown case makes the sum unknown.
 *
 * <p>Numbers too large to hold come back as {@link #UNKNOWN}. Losing a bound is losing precision and
 * nothing else — the comparisons this feeds are all of the form "is this too small to fill that", and
 * an answer of no is what a caller does nothing with.
 */
public final class Cardinality {

    /** No value of the type exists. */
    public static final Cardinality NO_VALUE = new Cardinality(0);

    /** No finite bound was proven. Not a count, and not comparable to one. */
    public static final Cardinality UNKNOWN = new Cardinality(-1);

    /** The bound, or -1 for {@link #UNKNOWN}. */
    private final long atMost;

    private Cardinality(long atMost) {
        this.atMost = atMost;
    }

    /** At most {@code count} values, which must not be negative. */
    public static Cardinality atMost(long count) {
        if (count < 0) {
            throw new IllegalArgumentException("a count of values is not negative: " + count);
        }
        return count == 0 ? NO_VALUE : new Cardinality(count);
    }

    /** Whether the type is known to have no value. */
    public boolean none() {
        return atMost == 0;
    }

    /** Whether no finite bound was proven. */
    public boolean unknown() {
        return atMost < 0;
    }

    /**
     * The bound, or {@code absent} where none was proven.
     *
     * <p>Handed back this way rather than thrown for, because every caller of it is about to decide
     * how far to enumerate and has an answer for the unknown case already.
     */
    public long boundOr(long absent) {
        return unknown() ? absent : atMost;
    }

    /**
     * Whether this is known to be no wider than {@code count} values.
     *
     * <p>No where nothing was proven. What is not known to be small is not known to be too small to
     * fill anything, and a reader taking the unknown for a small number refuses types that have
     * values.
     */
    public boolean noWiderThan(long count) {
        return !unknown() && atMost <= count;
    }

    /** Whether this admits at least as many values as {@code other}, the unknown admitting the most. */
    public boolean atLeastAsWideAs(Cardinality other) {
        return unknown() || (!other.unknown() && atMost >= other.atMost);
    }

    /**
     * The tighter of two bounds on one set of values.
     *
     * <p>Two readings of one position — what its type leaves and what the record around it leaves —
     * both hold, so the values are inside both and the smaller number is the one that is true of
     * them.
     */
    public static Cardinality narrower(Cardinality one, Cardinality other) {
        return one.atLeastAsWideAs(other) ? other : one;
    }

    /** A sum's cases, or an optional's {@code None} beside what it wraps. */
    public Cardinality plus(Cardinality other) {
        if (unknown() || other.unknown()) {
            return UNKNOWN;
        }
        long sum = atMost + other.atMost;
        return sum < 0 ? UNKNOWN : atMost(sum);   // a wrapped sum is a number too large to keep
    }

    /**
     * A record's fields.
     *
     * <p>Read before the unknown, because a factor of none is the answer whatever stands beside it.
     */
    public Cardinality times(Cardinality other) {
        if (none() || other.none()) {
            return NO_VALUE;
        }
        if (unknown() || other.unknown()) {
            return UNKNOWN;
        }
        try {
            return atMost(Math.multiplyExact(atMost, other.atMost));
        } catch (ArithmeticException tooLarge) {
            return UNKNOWN;
        }
    }

    /**
     * The lists of length {@code length} over these values.
     *
     * <p>One at length none — the empty list — whatever the element is, this being the one place a
     * type with no value still leaves a collection with one.
     */
    public Cardinality toThe(long length) {
        if (length < 0) {
            throw new IllegalArgumentException("a length is not negative: " + length);
        }
        if (length == 0) {
            return atMost(1);
        }
        if (unknown()) {
            return UNKNOWN;
        }
        long product = 1;
        for (long each = 0; each < length; each++) {
            try {
                product = Math.multiplyExact(product, atMost);
            } catch (ArithmeticException tooLarge) {
                return UNKNOWN;
            }
            if (product == 0) {
                return NO_VALUE;
            }
        }
        return atMost(product);
    }

    /**
     * The subsets of size {@code size} over these values.
     *
     * <p>None where the size asks for more values than there are, which is the whole of what a set
     * asking to be filled from too small an element comes to.
     */
    public Cardinality choose(long size) {
        if (size < 0) {
            throw new IllegalArgumentException("a size is not negative: " + size);
        }
        if (unknown()) {
            return UNKNOWN;
        }
        if (size > atMost) {
            return NO_VALUE;
        }
        long taken = Math.min(size, atMost - size);
        long ways = 1;
        for (long each = 1; each <= taken; each++) {
            try {
                // Multiplied before divided, and the division is exact: the product of `each`
                // consecutive numbers is divisible by `each` factorial as it is reached.
                ways = Math.multiplyExact(ways, atMost - taken + each) / each;
            } catch (ArithmeticException tooLarge) {
                return UNKNOWN;
            }
        }
        return atMost(ways);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof Cardinality that && atMost == that.atMost;
    }

    @Override
    public int hashCode() {
        return Long.hashCode(atMost);
    }

    @Override
    public String toString() {
        return unknown() ? "unknown" : none() ? "none" : "at most " + atMost;
    }
}
