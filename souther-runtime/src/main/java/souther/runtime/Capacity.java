package souther.runtime;

/**
 * How many elements a {@code List}, a {@code Map} or a {@code Set} holds: as many as its size, an
 * {@code int}, counts.
 *
 * <p>None of them keeps its elements in one array, so no VM limit on an array is reached first —
 * the size is. One more than the largest would wrap the size to a negative number and leave a
 * collection that answers wrongly about itself, so it aborts instead, the same abort any answer
 * with no place is (spec §an-operation-refuses-only-what-its-own-answer-has-no-place-for). Each
 * collection asks this where it grows and nowhere else, so every operation that grows one is held
 * to it.
 */
final class Capacity {

    private Capacity() {}

    /** Aborts where a {@code container} already {@code size} long is asked to hold one more. */
    static void oneMore(int size, String container) {
        if (size == Integer.MAX_VALUE) {
            throw new ConstraintViolation(
                    "a " + container + " holds at most " + Integer.MAX_VALUE + " elements");
        }
    }
}
