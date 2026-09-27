package souther.runtime;

/**
 * How many elements a {@code List}, a {@code Map} or a {@code Set} holds (spec
 * §what-a-collection-holds).
 *
 * <p>The bound is a number of the language, the same for all three and on every carrier. The JVM
 * counts a size in an {@code int}, which happens to hold it exactly, but that is why it is
 * representable here and not why it is the bound. A collection within it is an ordinary allocation,
 * which the heap may still refuse, as it may any other; that refusal is the host's and is not an
 * answer with no place.
 *
 * <p>None of them keeps its elements in one array, so no VM limit on an array is reached first.
 * One more than the bound would wrap the size to a negative number and leave a collection that
 * answers wrongly about itself, so it aborts instead, the same abort any answer with no place is
 * (spec §an-operation-refuses-only-what-its-own-answer-has-no-place-for). Each collection asks
 * {@link #oneMore} where it grows and nowhere else, so every operation that grows one is held to
 * it; an operation that knows its answer's length first asks it up front.
 *
 * <p>The specification states the same number, and
 * {@code TheCollectionBoundTheSpecificationStatesIsTheOneTheRuntimeHoldsTest} keeps the two equal.
 */
public final class Capacity {

    /** The most elements a {@code List}, a {@code Map} or a {@code Set} holds. */
    public static final long MOST_ELEMENTS = 2_147_483_647L;

    private Capacity() {}

    /** Aborts where a {@code container} already {@code size} long is asked to hold one more. */
    static void oneMore(int size, String container) {
        if (size >= MOST_ELEMENTS) {
            throw new ConstraintViolation(
                    "a " + container + " holds at most " + MOST_ELEMENTS + " elements");
        }
    }

    /** Aborts where the consecutive integers from {@code from} to {@code to}, both included, are
     *  more than {@code most}. Nothing is built, and {@code to - from} is not formed where it can
     *  overflow. The caller has already taken {@code from} above {@code to} as the empty span. */
    static void span(long from, long to, long most) {
        long width = to - from + 1;
        // A width that wrapped is negative or zero: the true one is past what a long counts.
        if (width <= 0 || width > most) {
            throw new ConstraintViolation("List.rangeInclusive is out of range: " + from + " to " + to);
        }
    }
}
