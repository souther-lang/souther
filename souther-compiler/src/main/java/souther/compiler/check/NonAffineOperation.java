package souther.compiler.check;

/**
 * Which arithmetic no form over the atoms says, as the rule that met it decided.
 *
 * <p>Decided where the operation is composed ({@link Terms#product}, {@link Terms#quotient}) and
 * carried from there, so that nothing downstream reads the expression again to guess which
 * operator it stopped at. The operands are non-constant forms, which are not always an input's
 * numbers: that they are is what a report adds from what it knows of the place.
 */
public enum NonAffineOperation {

    /** A product of two forms neither of which is a constant. */
    PRODUCT_OF_NON_CONSTANT_VALUES,

    /** A quotient by a form that is not a constant. */
    DIVISION_BY_NON_CONSTANT_VALUE,

    /** An operator that answers no number, so there is no arithmetic for a form to say. */
    NO_NUMBER_OF_ARITHMETIC;

    /** Whether this is arithmetic whose shape a report can name, and not an operator with none. */
    public boolean isArithmetic() {
        return this != NO_NUMBER_OF_ARITHMETIC;
    }
}
