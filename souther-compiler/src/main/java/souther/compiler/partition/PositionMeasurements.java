package souther.compiler.partition;

import java.util.List;

/**
 * One position of a behavior's input, and the numbers this phase measured it at.
 *
 * <p>The measures a location has are held under the location, because that is the relation the
 * model states: a location is measured at as many numbers as the rules name of it, and none, one or
 * several is the whole of what can be there. Held in a list of its own beside a list of locations,
 * the relation is in neither of them — and the only way back to it is to compare how each is
 * spelled, which is a reading of the paths invented once per reader and free to answer differently
 * from the reading that made them.
 *
 * <p>Empty where nothing measures the location, which is an answer and not an absence to fill in. A
 * position the rules divide nowhere is still a position this phase answers for: a report names it,
 * and a rule read later can still be the first to draw a line there.
 *
 * @param position what the location is and what its reading came to, true of it once however many
 *                 numbers measure it
 * @param axes     the measures made of it, in the order the rules name the numbers
 */
public record PositionMeasurements(PositionAccount position, List<Axis> axes) {

    public PositionMeasurements {
        if (position == null) {
            throw new IllegalArgumentException("measures of no position");
        }
        axes = List.copyOf(axes);
        for (Axis axis : axes) {
            held(position, axis);
        }
    }

    /**
     * That {@code axis} is a measure of this position, which is what holding it here says.
     *
     * <p>Checked where the two are put together and nowhere else. An axis names the position its
     * number is taken of, so which position a measure belongs to has two spellings the moment one is
     * held under the other — and a reader that met them apart would have to decide which of the two
     * to believe. Asked here once, every reader afterwards has the answer by where the measure sits.
     */
    private static void held(PositionAccount position, Axis axis) {
        if (!axis.term().position().equals(position.path())) {
            throw new IllegalArgumentException("`" + axis.id() + "` measures a number of "
                    + axis.term().position() + ", and is held under " + position.path());
        }
        if (!axis.type().equals(position.type())) {
            throw new IllegalArgumentException("`" + axis.id() + "` reads a value of "
                    + axis.type() + " where " + position.path() + " holds " + position.type());
        }
        if (!axis.id().behavior().equals(position.behavior())) {
            throw new IllegalArgumentException("`" + axis.id() + "` is a measure of another"
                    + " behavior's input than " + position.path() + " of " + position.behavior());
        }
    }

    /** The same position, measured at what a body's rules added to it. */
    public PositionMeasurements measuredAt(List<Axis> axes) {
        return new PositionMeasurements(position, axes);
    }
}
