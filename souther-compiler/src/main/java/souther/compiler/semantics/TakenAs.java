package souther.compiler.semantics;

import souther.compiler.types.Type;

/**
 * How the number an operation answers is taken of the one value it is given.
 *
 * <p>A strategy identity and nothing more. What such a number is measured by, where it runs, and
 * whether every number it could give is one some value gives are three other propositions, each
 * declared on its own — a carrier read off an arm here would put the operation's result type back
 * inside the classification the arm is, which is what {@code inputs.NumericTerm.SizeOf} was and what
 * splitting it up is for (#1027).
 *
 * <p>What an arm settles is how the number is read off an observation of the value. Whether values
 * answering a given number can be built is a second question, asked of the same account and
 * answered where rows are composed ({@code partition.TermRealizations}) — and whether every number
 * such an operation could answer has a value that gives it is a third, declared of the operation
 * ({@code EveryAnswerItCanGiveHasASourceValue}).
 *
 * <p><b>Three questions and not one, so an arm may answer the first and not the second.</b> An
 * account whose building nothing here does is an operation a boundary is found on and no row
 * composed for, which is what {@code NOTHING_COMPOSES_ONE} says of a point; read as an obligation to
 * write something, the arm added next would get whatever its author could make return a value, and
 * a row offered at an edge it does not stand on is worse than no row. What must hold of what is
 * built is one way round — every value built reads back as the number it was built for — and that
 * is stated where the building is.
 *
 * <p>Neither direction is written here. This says which account it is; the reading is the reader's
 * ({@code inputs.NumericTerm}) and the building is the generator's ({@code partition}), for the same
 * reason {@link Arithmetic} names an arithmetic and leaves the term to whoever holds the call.
 */
public sealed interface TakenAs {

    /**
     * Whether a value of {@code source} is what this is taken of, for an operation answering
     * {@code answered}.
     *
     * <p>Held to the library's own signature ({@code check.OperationFactBinder}), so an operation
     * declared with an arm it is not the shape of is refused where the declaration is written rather
     * than read as that arm at a row.
     */
    boolean takenOf(Type source, Type answered);

    /**
     * How many a container holds: a string's length, a list's, the size of a set or a map.
     *
     * <p>Counted in what the library counts in — a string in code points, as {@code String.length}
     * does.
     */
    record HowManyItHolds() implements TakenAs {

        @Override
        public boolean takenOf(Type source, Type answered) {
            return answered == Type.Prim.INT
                    && (source == Type.STRING || source instanceof Type.ListOf
                            || source instanceof Type.SetOf || source instanceof Type.MapOf);
        }
    }

    /**
     * What a container holds added up.
     *
     * <p>Not declared of an operation beside the walk it is. What {@code List.sum} does is stated
     * once, as the accumulation it is — start from nought, carry addition — and this arm is that
     * statement read as a way of taking a number. Written down a second time here, a sum would be
     * nought and addition to whoever discharges a rule about it and something else to whoever
     * measures one, with nothing bringing the two together to disagree.
     *
     * <p>Which is why the arm carries no arithmetic of its own. It says which account it is; what
     * the account comes to is the accumulation's, and a reader wanting the identity or the step asks
     * there.
     *
     * <p>Read off every element, so the number is what the values at the position add up to and not
     * what any one of them is. A container holding nothing adds up to nought, which is the identity
     * the walk starts from and not an absence.
     */
    record TheSumOfWhatItHolds() implements TakenAs {

        @Override
        public boolean takenOf(Type source, Type answered) {
            // A container of what it answers, which is what carrying the answer so far through one
            // step over two values of that type comes to. Nothing here about the elements being
            // numbers: which of them this language admits is settled where a call is typed, and
            // what may be read as a number is asked of the answer afterwards.
            Type element = Type.elementOfAContainer(source);
            return element != null && element.equals(answered);
        }
    }

    /**
     * Which part of a time of day it is: the hour it falls in, the minute within that hour, the
     * second within that minute.
     *
     * <p>One arm for the three and not one each. What tells them apart is which part is taken, and a
     * part is a value rather than a kind of question — written as three arms, the next reader to add
     * one would be adding a way of taking a number rather than a member of a family that already
     * has a way, and the two directions would each grow a case for it (#1027).
     *
     * <p>The clearest case of the two ends of a term being two orders. A time is counted in seconds
     * of its day and what these answer is counted by one, so what a boundary on the hour is drawn on
     * is not what the value at the position is read on. Both taken from one carrier, a line at the
     * thirteenth hour would be a line at the thirteenth second.
     */
    record PartOfTime(TimePart part) implements TakenAs {

        public PartOfTime {
            java.util.Objects.requireNonNull(part, "this one says which part");
        }

        @Override
        public boolean takenOf(Type source, Type answered) {
            return source == Type.Prim.TIME && answered == Type.Prim.INT;
        }
    }

    /**
     * Which part of a date it is: the year it falls in, the month within that year, the day within
     * that month.
     *
     * <p>Beside {@link PartOfTime} and not one arm with it. Both take a component out of a value the
     * library counts, and there the likeness stops: the parts of a day are a fixed-radix system, so
     * a division and a remainder answer any of them and the two directions are written once for the
     * family. The parts of a date are the calendar's, and no arithmetic over the day count answers
     * them — a month is not a number of days. One arm covering both would carry the account of two
     * different things, and whichever of the two was written first would be the shape the other had
     * to be squeezed into.
     *
     * <p>So the part is a name and carries no arithmetic, and what a year, a month and a day are is
     * the calendar's to say where the count is turned into a date. Given a step and a modulus here,
     * as the parts of a day have, the numbers would be wrong for eleven months in twelve.
     */
    record PartOfDate(DatePart part) implements TakenAs {

        public PartOfDate {
            java.util.Objects.requireNonNull(part, "this one says which part");
        }

        @Override
        public boolean takenOf(Type source, Type answered) {
            return source == Type.Prim.DATE && answered == Type.Prim.INT;
        }
    }

    /** A part of a date, in the order the parts run. */
    enum DatePart {

        /** The year it falls in. */
        YEAR,

        /** The month within that year, counted from one. */
        MONTH,

        /** The day within that month, counted from one. */
        DAY
    }

    /** A part of a time of day, in the order the parts run. */
    enum TimePart {

        /** The hour it falls in, of the twenty-four a day has. */
        HOUR(3600, 24),

        /** The minute within that hour. */
        MINUTE(60, 60),

        /** The second within that minute. */
        SECOND(1, 60);

        private final int seconds;
        private final int many;

        TimePart(int seconds, int many) {
            this.seconds = seconds;
            this.many = many;
        }

        /** How many seconds one of these is worth, which is what reading and writing both count
         *  in: a time is a count of seconds into its day and this is the step that count moves by. */
        public int seconds() {
            return seconds;
        }

        /** How many of these there are before the part above it turns over. */
        public int many() {
            return many;
        }
    }
}
