package souther.compiler.abort;

/**
 * How far from nought the scale of a {@code Decimal} is at most, and how many digits its number
 * has at most, said over what a call is handed: what a reader of a run reads off the arguments it
 * has, and the owner of an operation says without having them
 * ({@link GetsPast.WhereTheScalesHaveRoom}).
 *
 * <p>A bound and not a scale. What a run is at is no business of the owner of an operation, and
 * the bound it states holds over every run: the larger of two, what a law makes of two others.
 */
public sealed interface ScaleBound {

    /** The shape of the argument at {@code at}, counted from nought, a number. */
    record Argument(int at) implements ScaleBound {}

    /** The scale asked for by the whole number written at the argument {@code at}. */
    record WrittenAt(int at) implements ScaleBound {}

    /** A number written out at {@code scale} places, of {@code digits} digits. */
    record Written(long scale, long digits) implements ScaleBound {}

    /** What an operation under {@code law} leaves of two numbers at {@code first} and
     *  {@code second}. */
    record Left(ScaleLaw law, ScaleBound first, ScaleBound second) implements ScaleBound {}

    /** The larger of what either is: the number is one or the other. */
    record Larger(ScaleBound one, ScaleBound other) implements ScaleBound {}

    /** Nothing is said of the scale. */
    record NotShown() implements ScaleBound {}
}
