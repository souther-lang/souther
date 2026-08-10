package souther.compiler.partition;

/**
 * A position no class came back for, and which of the two that is.
 *
 * <p>The list of these used to be a list of paths, and everything downstream read a path in it as the
 * model having no distinction to draw there. A position whose rule is written in a form this does not
 * read is in that same list, and saying the same sentence about both tells an author to stop looking
 * for the line their own body draws.
 *
 * <p>So the absence is a value that has to be produced rather than the default reading of an empty
 * result. {@link Absent} is only written where the walk ran to the end and found nothing; where it
 * stopped, or where something named the position and this could not turn it into a line,
 * {@link CannotDerive} says so and carries which.
 *
 * @param at  the position, spelled the way a report names it
 * @param why whether the model draws nothing here or this could not read what it draws
 */
public record UndividedPosition(TermPath at, Why why) {

    /** Which of the two it is. */
    public sealed interface Why {

        /** The walk finished and the model divides this position no way at all. */
        record Absent() implements Why {}

        /** Something is written here that this did not read, so nothing is established either way. */
        record CannotDerive(Reason reason) implements Why {}
    }

    /**
     * What stopped the derivation.
     *
     * <p>Each of these is a fact about this compiler. They are told apart because they are lifted by
     * different work: one wants a reader for a form of condition, one wants the walk to go deeper,
     * and a report that named neither could not say which.
     */
    public enum Reason {
        /** A comparison this position is named by sits inside a condition this does not read. */
        UNSUPPORTED_SYNTAX,
        /** The values the comparison is against are not ones a line can be drawn on here. */
        UNSUPPORTED_DOMAIN,
        /** The walk stopped before it reached the fields under this position. */
        DEPTH_LIMIT
    }

    public static UndividedPosition absent(TermPath at) {
        return new UndividedPosition(at, new Why.Absent());
    }

    public static UndividedPosition cannotDerive(TermPath at, Reason reason) {
        return new UndividedPosition(at, new Why.CannotDerive(reason));
    }

    /** The same position, with a reason where it had none. A position already carrying one keeps it:
     * what stopped the walk first is what a reader has to lift first. */
    public UndividedPosition because(Reason reason) {
        return why instanceof Why.Absent ? cannotDerive(at, reason) : this;
    }

    public boolean isAbsent() {
        return why instanceof Why.Absent;
    }
}
