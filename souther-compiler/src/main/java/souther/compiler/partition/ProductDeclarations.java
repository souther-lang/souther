package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.NumericDomain;

/**
 * What the declarations leave the numbers of a product, for choosing where the number beside the
 * one alone stands to hold the product at a value
 * ({@link NumericTerm.ProductOf#standingWhereTheDeclarationsAdmit}).
 *
 * <p>Asked of the declarations alone, and not of what a way leaves a row: the choice is a fact of
 * the product, read the same wherever it is read, so the term that reads the product and the term
 * that writes it are one.
 */
final class ProductDeclarations implements NumericTerm.ProductOf.Declared {

    private final InputReading read;

    private ProductDeclarations(InputReading read) {
        this.read = read;
    }

    /** {@code product}, standing where the declarations of {@code read} admit — as it is where
     *  there is no reading to ask. */
    static NumericTerm.ProductOf.Signed admitted(NumericTerm.ProductOf.Signed product,
                                                 InputReading read) {
        return read == null ? product : new NumericTerm.ProductOf.Signed(product.product()
                .standingWhereTheDeclarationsAdmit(new ProductDeclarations(read)),
                product.sign());
    }

    @Override
    public NumericDomain.Bounds runOf(NumericTerm number) {
        return number instanceof NumericTerm.ValueOf value
                ? UndividedByARelation.everyValueTheDeclarationsLeave(value, read, false) : null;
    }

    @Override
    public boolean isDense(NumericTerm number) {
        TermOrders orders = read.quantities().ordersOf(number);
        return orders != null && orders.answered() instanceof Carrier.Dense;
    }
}
