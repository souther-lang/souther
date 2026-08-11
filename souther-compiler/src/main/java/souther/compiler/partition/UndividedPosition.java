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
        /**
         * The comparison relates two positions rather than dividing one.
         *
         * <p>`+x < y+` says where one position stands against another, and a class here is a set of
         * values of one position. Nothing is missing from the carrier — both sides are ordered and a
         * line drawn on either against a number would be read — so saying the values cannot carry a
         * line would send a reader after the wrong thing entirely.
         */
        UNSUPPORTED_PARTITION_SHAPE,
        /** The walk stopped before it reached the fields under this position. */
        DEPTH_LIMIT,
        /**
         * The type at this position could not be interpreted, so nothing about its values is
         * established. A model carrying one compiles, which is why this is a word a report writes
         * rather than a state nothing reaches.
         */
        TYPE_UNRESOLVED,
        /**
         * The position holds its values inside something this does not reach into — the elements of
         * a collection, what an optional holds, what a map holds. One word for all of them: which
         * reaching is missing is a fact about this compiler, and the model reads the same either
         * way. What this compiler could not do is told apart internally
         * ({@link BlockReason.UnsupportedTraversal}).
         */
        UNSUPPORTED_TRAVERSAL
    }

    public static UndividedPosition absent(TermPath at) {
        return new UndividedPosition(at, new Why.Absent());
    }

    public static UndividedPosition cannotDerive(TermPath at, Reason reason) {
        return new UndividedPosition(at, new Why.CannotDerive(reason));
    }

    /** The same position, with a reason where it had none. A position already carrying one keeps it:
     * what stopped the walk first is what a reader has to lift first. */
    /**
     * The same position with {@code reason} where nothing has been said yet, and unchanged where
     * something has.
     *
     * <p>Fills rather than replaces, and that is a precedence: a reason already here came from the
     * reading that stopped at this position, and one offered now comes from a reader of some rule
     * that names it. Where the two describe one stop they describe it from different ends — the
     * elements of a collection cannot be reached, and a comparison naming a position inside one
     * cannot be turned into a line — and the first is the cause.
     *
     * <p>Load-bearing only since the structural reading began answering with reasons of its own.
     * Before that it answered {@link Why.Absent} everywhere but the depth limit, so whatever a rule
     * reader offered was what a report said, and a threshold on a list element was reported as a
     * comparison this cannot read rather than as elements this cannot reach.
     */
    public UndividedPosition because(Reason reason) {
        return why instanceof Why.Absent ? cannotDerive(at, reason) : this;
    }

    public boolean isAbsent() {
        return why instanceof Why.Absent;
    }
}
