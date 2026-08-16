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
 * result. {@link Why.Absent} is produced by {@link PendingPosition#complete} and nowhere else, from
 * a position whose structural reading did not stop and whose rules were all read and drew nothing —
 * which is what the word means. Where the reading stopped, or where something named the position
 * and this could not turn it into a line, {@link Why.CannotDerive} says so and carries which.
 *
 * @param at  the position, spelled the way a report names it
 * @param why whether the model draws nothing here or this could not read what it draws
 */
public record UndividedPosition(TermPath at, Why why) {

    /** Which of the two it is. */
    public sealed interface Why {

        /**
         * Every reading ran to the end, none of them stopped, and none of them divided the
         * position: the model divides it no way at all.
         *
         * <p>A class with no way to make one rather than a record, because what it says is a
         * conclusion about a model and the only thing entitled to draw it is the completion of a
         * {@link PendingPosition}. Anything able to write {@code new Absent()} is able to say the
         * model divides a position no way without having asked anything, which is the sentence this
         * whole protocol exists to stop being cheap to write.
         */
        final class Absent implements Why {

            /** The one, reached through {@link PendingPosition#complete}. */
            static final Absent PROVEN = new Absent();

            private Absent() {}

            @Override
            public boolean equals(Object other) {
                return other instanceof Absent;
            }

            @Override
            public int hashCode() {
                return Absent.class.hashCode();
            }

            @Override
            public String toString() {
                return "Absent";
            }
        }

        /** Something is written here that this did not read, so nothing is established either way. */
        record CannotDerive(Reason reason) implements Why {}
    }

    /**
     * What stopped the derivation, in the words a document is written in.
     *
     * <p>Each of these is a fact about this compiler, said at the coarseness a reader of a document
     * is promised. They are told apart because they are lifted by different work: one wants a
     * reader for a form of condition, one wants the walk to go deeper, and a report that named
     * neither could not say which.
     *
     * <p>Not the cause itself. What a producer recorded is a {@link BlockReason}, and one of these
     * is what {@link ReportedReason} projects it to — three missing traversals arrive here as one
     * word. So a reader of this knows which kind of thing stopped the derivation and not which
     * capability was missing.
     */
    public enum Reason {
        /**
         * A rule about this position is one this compiler did not read.
         *
         * <p>Said of the rule and not of one way of failing to read it. A comparison inside a
         * condition this does not take apart is one; a rule naming which values may stand here,
         * written as something other than a value written out, is another; a rule this never
         * reached at all is a third. The word is the whole of what a reader is promised — that the
         * model states something here and this compiler did not read it — and which reader of the
         * clause gave up is not part of the promise.
         */
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

    /**
     * The absence, of a position that has been completed.
     *
     * <p>The argument is the proof. A {@link PendingPosition} is made from a position whose local
     * producers all came back with nothing, and only completing one reaches this — so what cannot
     * happen is an absence written by a reader that did not ask. Outside this package there is
     * neither a way to make one of those nor a name for this.
     */
    static UndividedPosition absentAfter(PendingPosition proven) {
        return new UndividedPosition(proven.at(), Why.Absent.PROVEN);
    }

    static UndividedPosition cannotDerive(TermPath at, Reason reason) {
        return new UndividedPosition(at, new Why.CannotDerive(reason));
    }

    public boolean isAbsent() {
        return why instanceof Why.Absent;
    }
}
