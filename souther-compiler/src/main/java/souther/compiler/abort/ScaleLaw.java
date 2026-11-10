package souther.compiler.abort;

import souther.compiler.types.BinOp;

/**
 * How a decimal operation leaves the scale of its answer from the scales of two numbers it works
 * on, which is what decides whether a run has room for it ({@link GetsPast.WhereTheScalesHaveRoom}).
 *
 * <p>Said by the owner of each operation and read, with the arithmetic of scales, by whoever asks
 * whether the scales have room: a row and a witness are asked by the same rule
 * ({@code DecimalOperation}).
 */
public sealed interface ScaleLaw {

    /** Which argument is the first of the two scales, counted from nought. */
    int firstAt();

    /** Which argument is the second of the two scales, counted from nought. */
    int secondAt();

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

        @Override
        public int firstAt() {
            return 0;
        }

        @Override
        public int secondAt() {
            return 1;
        }
    }

    /**
     * The answer is at the scale the call asks for, a whole number it writes out at
     * {@code scaleAt}, of the number at {@code operandAt}: a rounding to a number of places.
     *
     * @param scaleAt   which argument is the scale asked for
     * @param operandAt which argument is the number it is made at that scale
     */
    record Asked(int scaleAt, int operandAt) implements ScaleLaw {

        @Override
        public int firstAt() {
            return scaleAt;
        }

        @Override
        public int secondAt() {
            return operandAt;
        }
    }
}
