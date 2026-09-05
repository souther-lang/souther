package souther.compiler.partition;

/**
 * What a walk down a path came to, where a walk is a thing that may not be possible to take.
 *
 * <p>Two questions and not one. Whether a path can be walked at all is settled by the declarations
 * and the value in hand, and what stands at the end of it is settled by the row — and a walk that
 * could not be taken has no answer to the second, so it answers the first instead of handing back
 * an emptiness a reader has to give a meaning to. Answered with one shape, the two arrive as one
 * word downstream: a place this compiler could not reach is reported as a place a row wrote
 * nothing, which is news about the model where nothing about the model was found out.
 *
 * <p><b>What {@link Reached} holds may itself hold nothing.</b> A walk that arrived and found the
 * row standing nowhere below it is a walk that arrived, and its emptiness is an answer rather than
 * the lack of one. That is the whole distinction this type exists to keep, so a reader that means
 * to ask about the row asks it of what {@code Reached} carries and never of which of these two came
 * back.
 *
 * @param <T> what the walk answers with where it was taken
 */
public sealed interface WalkResult<T> {

    /** The walk was taken, and this is what it came to. */
    record Reached<T>(T value) implements WalkResult<T> { }

    /** The walk could not be taken, so there is nothing it came to. */
    record CouldNotWalk<T>() implements WalkResult<T> { }

    /** The walk taken, answering with {@code value}. */
    static <T> WalkResult<T> reached(T value) {
        return new Reached<>(value);
    }

    /** The walk not taken, which every caller says the same way. */
    static <T> WalkResult<T> couldNotWalk() {
        return new CouldNotWalk<>();
    }
}
