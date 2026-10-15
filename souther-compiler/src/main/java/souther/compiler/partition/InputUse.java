package souther.compiler.partition;

/**
 * Whether anything a behavior states reads the value at one position of its input.
 *
 * <p>Beside {@link BodyDistinction} and not a fourth answer of it. That one says which classes the
 * ways a run takes tell apart, and a value copied into the answer is told apart by none of them
 * while every class of it comes out differently. This one says whether the value is read at all —
 * by the body or by a clause of the behavior — and nothing about what is made of it.
 *
 * <p><b>Only {@link NotRead} excuses a class its row.</b> A row at a class of a position nothing
 * reads gives the answer a row at any other class of it gives, so it checks nothing a row beside it
 * did not. A position whose reading was not settled may be read, and is owed what a read one is.
 */
public sealed interface InputUse {

    /** Something the behavior states reads the value, or a value it stands under. */
    record Read() implements InputUse {}

    /**
     * Everything the behavior states was read, and none of it reads the value. A value the position
     * sits under being read for another of its fields does not read this one.
     */
    record NotRead() implements InputUse {}

    /**
     * Whether the value is read is not known: there is no body to read, a clause was not made into
     * an expression, or a parameter was read where no position could be named for it.
     */
    record NotKnown() implements InputUse {}

    /** Whether a row at each class of the position checks something a row at another does not. */
    default boolean owesARowPerClass() {
        return !(this instanceof NotRead);
    }
}
