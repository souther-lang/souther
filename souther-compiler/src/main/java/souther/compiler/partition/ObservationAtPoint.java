package souther.compiler.partition;

import souther.compiler.observe.ObservedValue;

/**
 * What a row holds at one position, where the walk to that position was taken.
 *
 * <p>Under {@link WalkResult} and not beside it. Whether the walk could be made is a question about
 * the declarations and this compiler's reading of them; these are answers about the row, and a walk
 * that was refused has none of them. Laid out flat with a fourth arm for the refusal, a reader
 * switching over them would be told that not having looked is one of the things a row can hold —
 * which is the shape that had the two arriving as one word to begin with.
 *
 * <p>Each says what happened and none of them says what a reader should do about it. What a
 * quantity concludes from a row that stands nowhere is the quantity's, and it changes without these
 * changing.
 */
public sealed interface ObservationAtPoint {

    /** One value of the row stands here. */
    record Value(ObservedValue value) implements ObservationAtPoint { }

    /** The row wrote nothing at this position, so nothing of it stands anywhere below. */
    record WroteNothing() implements ObservationAtPoint { }

    /**
     * The row's values here were reached through elements this reading did not choose.
     *
     * <p>A row inside a sequence has as many values at a position as it wrote, and standing at a
     * point is one element standing there — so a reading names an element per step, and a position
     * whose values are all under other elements holds none under this one. Another reading of the
     * same row is where they are.
     */
    record BelongsToAnotherReading() implements ObservationAtPoint { }

    ObservationAtPoint WROTE_NOTHING = new WroteNothing();

    ObservationAtPoint ANOTHER_READING = new BelongsToAnotherReading();
}
