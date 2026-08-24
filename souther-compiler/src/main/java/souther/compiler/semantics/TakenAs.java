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
     * How far from nought a number stands, which is the number with its sign dropped.
     *
     * <p>Over the operation's own kind of number and not over a count: {@code Decimal.abs} answers
     * a decimal, so the values beside a boundary on it are the decimals and not the whole numbers
     * either side. That is the half a term measured by what the operation is a kind of could not
     * have said.
     */
    record AbsoluteMagnitude() implements TakenAs {

        @Override
        public boolean takenOf(Type source, Type answered) {
            return source.equals(answered)
                    && (answered == Type.Prim.INT || answered == Type.Prim.DECIMAL);
        }
    }
}
