package souther.compiler.semantics;

/**
 * Which of two arguments a positive answer names as the greater.
 *
 * <p>That is the whole of what such an operation says, and it is two cases, so it is written as a
 * type with two — not as one of the language's operators, which would say the same thing in a type
 * where most of the values say nothing and the ones that do have to be agreed on somewhere else.
 *
 * <p>Each case carries both arguments itself, since which is the lesser is settled by which is the
 * greater and there is no reading where the two are chosen apart.
 */
public enum PositiveOrder {

    FIRST_ARGUMENT_GREATER(0, 1),
    SECOND_ARGUMENT_GREATER(1, 0);

    private final int greater;
    private final int lesser;

    PositiveOrder(int greater, int lesser) {
        this.greater = greater;
        this.lesser = lesser;
    }

    /** The argument a positive answer names as the greater. */
    public ArgumentRef greater() {
        return new ArgumentRef.At(greater);
    }

    /** The other one. */
    public ArgumentRef lesser() {
        return new ArgumentRef.At(lesser);
    }
}
