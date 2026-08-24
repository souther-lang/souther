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
 * <p>What an arm does settle is a pair: reading the number off an observation of the value, and
 * building values that answer a given number. The two are one arm because they are one account of
 * the same operation read in two directions, and an arm added without both is an operation a
 * boundary can be found on and no row written for — a string counted in code points and written in
 * UTF-16 units is the same defect a size down.
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
