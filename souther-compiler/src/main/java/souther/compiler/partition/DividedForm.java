package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;

/**
 * A form of a row's numbers and the number it is divided by: what a row is asked to work a
 * remainder out of.
 *
 * <p>What a line on the remainder reads a row at, without the line — so a statement about the
 * remainder asked of a row reads the numbers the line does, and the remainder is worked out of
 * them the same way ({@link OrderedAffineBoundary#remainderAt}).
 *
 * @param numbers the numbers of the form, read at a row
 * @param whole the form the division is of, with its constant as a whole number
 * @param divisor the number it is divided by, above nought
 */
record DividedForm(LinearQuantity numbers, LinearForm<NumericTerm> whole, BigInteger divisor) { }
