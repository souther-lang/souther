package souther.compiler.partition;

import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.PositionId;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;

import java.util.List;

/**
 * One behavior's input as it was read, and where the model divides it.
 *
 * <p><b>Made from a reading and from nothing else.</b> The walk a row's values are written by, the
 * orders its numbers are measured on and the classes it is divided into all follow from one reading
 * of one behavior's declarations. Handed over as three values, a caller could hand a search the
 * walk of one reading and the orders of another — two behaviors taking a parameter spelled the same
 * way is all it takes, and then a row is composed on one reading's orders and read back by
 * another's walk. There is one argument here, so there is nothing to put together wrongly.
 *
 * <p><b>The reading itself does not come through.</b> What is offered is the two questions a search
 * asks — where a value is written, and what a number there is measured on — and not a way of asking
 * the reading anything else. A construction plan's coordinate is spelled with the same
 * {@link TermPath} as a position of the input, so a search that could reach the reading could look
 * one up in it and be told that a place it is building at is not a position of anything.
 */
public final class MeasuredInput {

    private final String behavior;
    private final BehaviorInputs written;
    private final Quantities quantities;
    private final List<Axis> axes;

    private MeasuredInput(String behavior, BehaviorInputs written, Quantities quantities,
                          List<Axis> axes) {
        this.behavior = behavior;
        this.written = written;
        this.quantities = quantities;
        this.axes = axes;
    }

    /**
     * The input {@code read} was made of, divided by {@code axes}.
     *
     * <p>The one way to make one. What a row is written by and what its numbers are measured on are
     * both taken from the reading rather than from the caller, and the axes are held to it: a
     * measure of a number the reading cannot answer for is a measure of another behavior's input,
     * whatever it is named after.
     *
     * @param behavior what the rows are written for, which every axis agrees with
     */
    public static MeasuredInput of(String behavior, InputReading read, List<Axis> axes) {
        if (behavior == null || behavior.isEmpty()) {
            throw new IllegalArgumentException("a row is written for a behavior with a name");
        }
        List<Axis> divided = List.copyOf(axes);
        for (Axis axis : divided) {
            // An axis of another behavior, which is a subject assembled from two measurements. The
            // name would then be one of two answers rather than the subject's, and whichever
            // sentence read it would be right about one of them.
            if (!axis.id().behavior().equals(behavior)) {
                throw new IllegalArgumentException(
                        "an axis of " + axis.id().behavior() + " in the subject of " + behavior
                                + ": " + axis.id());
            }
            // And a measure of a number this reading takes nothing of, which is what an axis
            // derived at another reading of a behavior spelled the same way comes to. The reading
            // refuses such a term, so asking it is the check.
            read.quantities().ordersOf(axis.term());
        }
        return new MeasuredInput(behavior, BehaviorInputs.of(read), read.quantities(), divided);
    }

    /**
     * Two of these are one where they were read and divided alike.
     *
     * <p>Written out because this is held in an answer, and what an answer holds is compared by
     * whatever decides that a compile changed nothing. The reading itself compares as the capability
     * it is — one per behavior per compile — so what this says is what the record it replaced said.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof MeasuredInput that
                && behavior.equals(that.behavior)
                && written.equals(that.written)
                && quantities.equals(that.quantities)
                && axes.equals(that.axes);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(behavior, written, quantities, axes);
    }

    @Override
    public String toString() {
        return "MeasuredInput[" + behavior + " over " + axes.size() + " axes]";
    }

    /** What the rows are written for. */
    public String behavior() {
        return behavior;
    }

    /**
     * The walk into what a row writes: what the inputs are called, what they are, and what those
     * names denote.
     *
     * <p>For composing a value and for reading one back, and for neither of the two questions
     * below. What a number at a position is measured on is the reading's
     * ({@link #quantities()}), and where the model divides one is the measure's.
     */
    public BehaviorInputs inputs() {
        return written;
    }

    /** What the rules reaching this input leave its numbers. */
    public Quantities quantities() {
        return quantities;
    }

    /** Where the model divides its positions. */
    public List<Axis> axes() {
        return axes;
    }

    /**
     * The same three facts a row is read by, which is the point of holding one value.
     *
     * <p>Written out here as well, a row would be generated from one reading of what the behavior
     * takes and read back by another — and how a position is written is exactly what the two came
     * to disagree about.
     */
    public List<String> parameters() {
        return written.parameters();
    }

    public List<Type> types() {
        return written.types();
    }

    public Symbols symbols() {
        return written.symbols();
    }

    /** How many the rules leave the container at {@code at}, or every number where they leave it
     *  unsaid. */
    public int mostHeldAt(PositionId at) {
        return quantities.mostHeldAt(at);
    }

    /**
     * Whether the model divides this position into a class spelled this way.
     *
     * <p>The one place the question is answered. A reader working it out from a partition's axes
     * beside this one is a second reading of what a search's own universe is, and the two agree
     * until either moves — which is how a case of an input came to be told there was no axis at its
     * position by one reading while the search had classes there under the other.
     */
    public boolean divides(Generator.ClassOwed owed) {
        for (Axis axis : axes) {
            if (!axis.id().equals(owed.at())) {
                continue;
            }
            for (PartitionClass cls : axis.classes()) {
                if (cls.id().equals(owed.classId())) {
                    return true;
                }
            }
        }
        return false;
    }
}
