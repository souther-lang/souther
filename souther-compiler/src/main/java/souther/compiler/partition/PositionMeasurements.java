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
 * @param position   what the location is and what its reading came to, true of it once however many
 *                   numbers measure it
 * @param axes       the measures made of it, in the order the rules name the numbers
 * @param inspection what the rules written about this location came to, over every number it is
 *                   measured at. One sentence for the location because that is what a report says
 *                   about one: written per measure, a location measured at two numbers is told
 *                   twice that it is divided nowhere, and told it at all where one of its numbers
 *                   is divided and another is not
 */
public record PositionMeasurements(PositionAccount position, List<Axis> axes,
                                   BodyCutInspection inspection) {

    public PositionMeasurements {
        if (position == null) {
            throw new IllegalArgumentException("measures of no position");
        }
        // What the rules came to is part of what this answers, so it is here before anything reads
        // it. A value without it is a location half answered for, and the readers of it — the
        // verdict a report writes about the location, and what it is left with — take it as the
        // answer rather than as something still to arrive.
        if (inspection == null) {
            throw new IllegalArgumentException(
                    position.path() + " has no account of what the rules written about it came to");
        }
        axes = List.copyOf(axes);
        java.util.Set<AxisId> named = new java.util.LinkedHashSet<>();
        for (Axis axis : axes) {
            held(position, axis);
            // One measure per number. What tells two measures of one location apart is the number
            // each is of, which is what names them, and every reader downstream holds them under
            // that name — a second measure of one number is one of them silently standing for the
            // other in a map, and two of them counted where a report counts measures.
            if (!named.add(axis.id())) {
                throw new IllegalArgumentException("`" + axis.id() + "` measures " + axis.term()
                        + " twice at " + position.path()
                        + "; a location is measured once at each number the rules name of it");
            }
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
    public PositionMeasurements measuredAt(List<Axis> axes, BodyCutInspection inspection) {
        return new PositionMeasurements(position, axes, inspection);
    }

    /**
     * Whether anything here has something to divide the location by — a class to cover, or a line
     * to reach.
     *
     * <p>Asked of the measures the location has, which is where the answer is. Not whether it has
     * any: a measure that only parts the number where the location holds no value has nothing at it
     * for a row to be written against, and a report telling an author what was measured here would
     * be naming work nobody can do. A location with no measure at all and one measured at a parting
     * nothing stands at come to the same thing for every reader of this.
     */
    public boolean measured() {
        return axes.stream().anyMatch(Axis::asksForARow);
    }

    /** The measures of this location that divide their number into classes. */
    public List<Axis> partitionAxes() {
        return axes.stream().filter(Axis::derivable).toList();
    }
}
