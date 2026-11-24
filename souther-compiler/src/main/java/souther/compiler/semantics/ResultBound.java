package souther.compiler.semantics;

import souther.compiler.numeric.Rel;

import java.math.BigDecimal;

/**
 * One bound an operation's result has, as the numeric domain holds bounds: the result against a
 * constant, or the result against one argument and a constant.
 *
 * <p>The shape is the domain's and is what a fact may say. A statement of another shape — a result
 * between two arguments, a result no greater than a sum — is one the domain would take in and
 * derive nothing from, so it is not writable here rather than written and silently dropped.
 *
 * <p><b>A bound is where a result stops, so {@link Rel#NE} is not one.</b> Everything else the
 * relations name is an end: an order names one, and an equality names both at once. A result that is
 * anything but one value is two ranges with a hole between them, which is not what this says and not
 * what either reader of it can carry — so it is refused here, where the representation is, and not
 * at the check that holds a fact to the library's signatures. That one asks whether a fact and a
 * declaration agree; this one is about what a bound is.
 *
 * <p>Generic in the word for an argument, as {@link ElementLineage} is: authored, the argument is
 * named as a fact writes it; held to the library, as the declaration has it.
 *
 * @param against  the argument the result is bounded against, or null where the bound is a constant
 *                 one
 * @param offset   added to that argument, or the constant itself where there is no argument
 * @param rel      how the result stands to it
 * @param provided what has to hold of the arguments for this to be the operation's answer
 * @param origin   whose line the end is: the operation's, or the place the representation stops
 * @param <A>      the word for an argument of the operation
 */
public record ResultBound<A>(A against, BigDecimal offset, Rel rel, Provided<A> provided,
                             Origin origin) {

    /** A bound that is a line of the operation. */
    public ResultBound(A against, BigDecimal offset, Rel rel, Provided<A> provided) {
        this(against, offset, rel, provided, new Origin.OfTheOperation());
    }

    public ResultBound {
        java.util.Objects.requireNonNull(offset, "a bound stands somewhere");
        java.util.Objects.requireNonNull(rel, "and stands some way to it");
        java.util.Objects.requireNonNull(provided, "and under some condition, `Always` if none");
        java.util.Objects.requireNonNull(origin, "and is somebody's line");
        if (rel == Rel.NE) {
            throw new IllegalArgumentException(
                    "a bound says where a result stops, and `NE` says where it does not stand: "
                            + against + " " + rel + " " + offset);
        }
        if (origin instanceof Origin.OfTheRepresentation && !statesAFixedEnd(against, rel, provided)) {
            throw new IllegalArgumentException("where the representation stops is one number the"
                    + " language keeps, so an end of it is not against an argument, not under a"
                    + " condition, and an order and not an equality: " + against + " " + rel
                    + " " + provided);
        }
    }

    private static boolean statesAFixedEnd(Object against, Rel rel, Provided<?> provided) {
        return against == null && provided instanceof Provided.Always<?>
                && (rel == Rel.LE || rel == Rel.GE);
    }

    /** Whether what a position is divided into is drawn to this end: a line of the operation, or a
     *  place the representation stops that is also an end of the type
     *  ({@link Limit#endsTheClasses}). */
    public boolean isDrawnTo() {
        return switch (origin) {
            case Origin.OfTheOperation _ -> true;
            case Origin.OfTheRepresentation(var limit) -> limit.endsTheClasses();
        };
    }

    /** Whether the end is where the representation stops, drawn to or not. */
    public boolean isWhereTheRepresentationStops() {
        return origin instanceof Origin.OfTheRepresentation;
    }

    /**
     * Whose line a bound is.
     *
     * <p>A length ends at nought because a count does, a line of the operation that a model writes
     * as the empty string. It ends above where a {@code String} stops, which is where a value cannot
     * stand and no distinction a model made. A reader asking whether a value can stand takes every
     * end; one asking what a position is divided into takes those that are drawn to.
     */
    public sealed interface Origin {

        /** The end is a line of the operation. */
        record OfTheOperation() implements Origin {}

        /**
         * The end is where the representation stops, named and not written: the number is read
         * where the bound is held to the library, from the one place the language's limit is
         * kept, because the declaring side cannot name that place.
         */
        record OfTheRepresentation(Limit limit) implements Origin {

            public OfTheRepresentation {
                java.util.Objects.requireNonNull(limit, "this one names the limit it stops at");
            }
        }
    }

    /**
     * A limit the language keeps, named where a fact is declared and given its number where the
     * fact is held to the library ({@code OperationFactBinder}). A declaration states no number
     * for one: a bound that is a limit carries zero until then, and the binder refuses a
     * declaration that wrote another.
     */
    public enum Limit {
        /** The most code points a {@code String} holds. Not an end of the classes of a length: the
         *  longest string is no distinction a model made, and a relation between two lengths would
         *  hold it as a class only a string of that length can fill. */
        LONGEST_STRING(false),
        /** The most elements a list or a set holds, and the most entries a map does. Not an end of
         *  the classes of a size, for the reason the longest string is not one. */
        MOST_ELEMENTS(false),
        /** The earliest year a date is written at. The first date is an end of the type, which
         *  every position of it is already divided at, so the year of a date runs to it. */
        EARLIEST_DATE_YEAR(true),
        /** The latest year a date is written at, an end of the type for the same reason. */
        LATEST_DATE_YEAR(true);

        private final boolean endsTheClasses;

        Limit(boolean endsTheClasses) {
            this.endsTheClasses = endsTheClasses;
        }

        /** Whether what a position is divided into is drawn to it. */
        public boolean endsTheClasses() {
            return endsTheClasses;
        }
    }

    /**
     * What has to hold of a call's arguments for the bound beside it to be what the operation
     * answers there.
     *
     * <p>A condition on the arguments and not on the result. An operation whose answer is bounded
     * only for some of the values it takes says so here, rather than being left out of the facts
     * for the values where the bound does not hold.
     *
     * <p>Whether a call meets one is read where calls are read; this says which condition it is.
     */
    public sealed interface Provided<A> {

        /** Nothing: the bound is what the operation does, whatever it is given. */
        record Always<A>() implements Provided<A> {}

        /**
         * An argument that stands above zero or below it.
         *
         * <p>What the condition says is this and only this; how an argument is found to stand so is
         * the reader's. One that can say only constants ({@link ConstantArguments}) holds it where
         * the argument reads as a constant that stands so, and one that holds a path holds it where
         * the path puts the argument there.
         *
         * <p>A constant is read and not written as one. What a name was given is what the name is,
         * wherever a value is read, so {@code floorMod(x, k)} under {@code let k = 100} is the same
         * call as {@code floorMod(x, 100)}. Requiring the digits at the call would make a rule an
         * author cannot predict from what the value is, only from where it was written.
         *
         * @param rel above zero ({@link Rel#GT}) or below it ({@link Rel#LT})
         */
        record ArgumentStands<A>(A argument, Rel rel) implements Provided<A> {

            public ArgumentStands {
                java.util.Objects.requireNonNull(argument, "this one names an argument");
                if (rel != Rel.GT && rel != Rel.LT) {
                    throw new IllegalArgumentException("an argument is above zero or below it,"
                            + " and was asked to stand " + rel);
                }
            }
        }
    }
}
