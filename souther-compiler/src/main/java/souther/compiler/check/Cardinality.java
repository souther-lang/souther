package souther.compiler.check;

/**
 * How many values a type has at most, or that no such number was proven, or that it has none.
 *
 * <p>An upper bound and never an exact count. What it is for is deciding that something cannot be
 * filled — a set of two needs two values of its element that differ — and for that the answer has to
 * be wide wherever the reading fell short. {@link Unknown} is that wide answer: not a large number,
 * but no number at all, and every question asked of it comes back the way that refuses nothing. It is
 * also what a shape the reading could not take in comes to, because a form nobody read is no reason to
 * refuse anything.
 *
 * <p>{@link None} is the other end and is a claim rather than an absence, so it is the one answer that
 * cannot be written without saying how it was shown. There is no constant for it and no arithmetic
 * reaches it: {@link Standing} is closed under everything the readings do, which leaves the named
 * places in {@link CardinalityTransfer} as the only way a count comes to nothing. A producer added
 * later has to name its proof to compile.
 *
 * <p>The product is where the two ends meet. A record is the product of what its fields hold, and a
 * field with no value leaves the record none however wide the field beside it is. That is not the
 * multiplication's doing — it is read off the field before anything is multiplied, which is also what
 * decides which field's proof the record carries.
 *
 * <p>Numbers too large to hold come back as {@link Unknown}. Losing a bound is losing precision and
 * nothing else — the comparisons this feeds are all of the form "is this too small to fill that", and
 * an answer of no is what a caller does nothing with.
 */
public sealed interface Cardinality {

    /** No value of the type exists, and the proof that showed it. */
    record None(Emptiness why) implements Cardinality {

        public None {
            if (why == null) {
                throw new IllegalArgumentException("a count of none is a claim and carries its proof");
            }
        }

        @Override
        public String toString() {
            return "none";
        }
    }

    /**
     * A count nothing has shown to be none.
     *
     * <p>Not a claim that a value exists — {@link Unknown} is here, and what it says is that the
     * reading proved no bound, which leaves the question open at both ends. What it is is the part of
     * the answers the arithmetic is closed over, so an operation on these can be written without a
     * proof to hand and without a way to reach none by accident.
     */
    sealed interface Standing extends Cardinality {

        /** A sum's cases, or an optional's {@code None} beside what it wraps. */
        default Standing plus(Standing other) {
            if (this instanceof Unknown || other instanceof Unknown) {
                return UNKNOWN;
            }
            long sum = ((AtMost) this).bound() + ((AtMost) other).bound();
            return sum < 0 ? UNKNOWN : atMost(sum);   // a wrapped sum is a number too large to keep
        }

        /** A record's fields, or a tuple's parts. */
        default Standing times(Standing other) {
            if (this instanceof Unknown || other instanceof Unknown) {
                return UNKNOWN;
            }
            try {
                return atMost(Math.multiplyExact(((AtMost) this).bound(), ((AtMost) other).bound()));
            } catch (ArithmeticException tooLarge) {
                return UNKNOWN;
            }
        }

        /**
         * The lists of length {@code length} over these values.
         *
         * <p>One at length none — the empty list — whatever the element is.
         */
        default Standing toThe(long length) {
            if (length < 0) {
                throw new IllegalArgumentException("a length is not negative: " + length);
            }
            if (length == 0) {
                return atMost(1);
            }
            if (this instanceof Unknown) {
                return UNKNOWN;
            }
            long each = ((AtMost) this).bound();
            long product = 1;
            for (long taken = 0; taken < length; taken++) {
                try {
                    product = Math.multiplyExact(product, each);
                } catch (ArithmeticException tooLarge) {
                    return UNKNOWN;
                }
            }
            return atMost(product);
        }

        /**
         * The subsets of size {@code size} over these values.
         *
         * <p>A size above how many values there are is not asked here. That a set cannot be filled
         * from its element is one comparison of two counts and is made where the set is read, so a
         * subset count reaching none would be that same refusal arrived at a second way and without a
         * proof to carry.
         */
        default Standing choose(long size) {
            if (size < 0) {
                throw new IllegalArgumentException("a size is not negative: " + size);
            }
            if (this instanceof Unknown) {
                return UNKNOWN;
            }
            long have = ((AtMost) this).bound();
            if (size > have) {
                throw new IllegalArgumentException(
                        "a set of " + size + " over " + have + " values is refused where it is read");
            }
            long taken = Math.min(size, have - size);
            long ways = 1;
            for (long each = 1; each <= taken; each++) {
                try {
                    // Multiplied before divided, and the division is exact: the product of `each`
                    // consecutive numbers is divisible by `each` factorial as it is reached.
                    ways = Math.multiplyExact(ways, have - taken + each) / each;
                } catch (ArithmeticException tooLarge) {
                    return UNKNOWN;
                }
            }
            return atMost(ways);
        }

        /**
         * The bound, or {@code absent} where none was proven.
         *
         * <p>Handed back this way rather than thrown for, because every caller of it is about to
         * decide how far to enumerate and has an answer for the unknown case already.
         */
        default long boundOr(long absent) {
            return this instanceof AtMost at ? at.bound() : absent;
        }

        /**
         * The tighter of two bounds on one set of values.
         *
         * <p>Two readings of one position — what its type leaves and what the record around it leaves
         * — both hold, so the values are inside both and the smaller number is the one that is true
         * of them.
         */
        static Standing narrower(Standing one, Standing other) {
            long here = one.boundOr(Long.MAX_VALUE);
            long there = other.boundOr(Long.MAX_VALUE);
            return here <= there ? one : other;
        }
    }

    /** At most this many values, which is at least one. */
    record AtMost(long bound) implements Standing {

        public AtMost {
            if (bound < 1) {
                throw new IllegalArgumentException(
                        "a count of none is written as a proof, not as a number: " + bound);
            }
        }

        @Override
        public String toString() {
            return "at most " + bound;
        }
    }

    /** No finite bound was proven. Not a count, and not comparable to one. */
    record Unknown() implements Standing {

        @Override
        public String toString() {
            return "unknown";
        }
    }

    /** No finite bound was proven. */
    Standing UNKNOWN = new Unknown();

    /** At most {@code count} values, which must be at least one. */
    static Standing atMost(long count) {
        return new AtMost(count);
    }

    /** No value at all, shown by {@code why}. */
    static Cardinality none(Emptiness why) {
        return new None(why);
    }

    /** Whether the type is known to have no value. */
    default boolean none() {
        return this instanceof None;
    }

    /** Whether no finite bound was proven. */
    default boolean unknown() {
        return this instanceof Unknown;
    }

    /** The proof that there is no value, or null where one was not shown. */
    default Emptiness why() {
        return this instanceof None it ? it.why() : null;
    }
}
