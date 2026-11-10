package souther.compiler.abort;

import souther.compiler.types.BinOp;

/**
 * How a decimal operation leaves the scale of its answer from the scales of two numbers it works
 * on, which is what decides whether a run has room for it ({@link GetsPast.WhereTheScalesHaveRoom}).
 *
 * <p>Said by the owner of each operation and read, with the arithmetic of scales, by whoever asks
 * whether the scales have room: a row and a witness are asked by the same rule
 * ({@code DecimalOperation}). Which numbers are the two is the site's to say
 * ({@link ScaleBound}), so a law is one rule of scales and nothing about where its operands stand.
 */
public sealed interface ScaleLaw {

    /**
     * A sum or a difference lines the two scales up and a product adds them.
     *
     * @param op the operator, add, subtract or multiply
     */
    record OfTheOperator(BinOp op) implements ScaleLaw {

        public OfTheOperator {
            if (op != BinOp.ADD && op != BinOp.SUB && op != BinOp.MUL) {
                throw new IllegalArgumentException("the scales of a decimal are lined up by a sum,"
                        + " a difference or a product, not " + op);
            }
        }
    }

    /** The answer is at the scale it is asked for, the first of the two, of the number at the
     *  second: a rounding to a number of places. */
    record Asked() implements ScaleLaw {}
}
