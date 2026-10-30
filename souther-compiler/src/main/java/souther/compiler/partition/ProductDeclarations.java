package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;

import java.util.LinkedHashMap;
import java.util.Map;

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

    /** {@code product}, standing where the declarations of {@code read} admit. */
    static NumericTerm.ProductOf.Signed admitted(NumericTerm.ProductOf.Signed product,
                                                 InputReading read) {
        return new NumericTerm.ProductOf.Signed(product.product()
                .standingWhereTheDeclarationsAdmit(new ProductDeclarations(read)),
                product.sign());
    }

    /** {@code form} with every product in it standing where the declarations of {@code read}
     *  admit; the same form where there is none. */
    static LinearForm<Quantity> admittedIn(LinearForm<Quantity> form, InputReading read) {
        if (form.coefs().keySet().stream().noneMatch(atom ->
                atom instanceof DecisionAtom.OfTheInput(NumericTerm.ProductOf _))) {
            return form;
        }
        ProductDeclarations declared = new ProductDeclarations(read);
        Map<Quantity, ExactRatio> out = new LinkedHashMap<>();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            Quantity atom = each.getKey() instanceof DecisionAtom.OfTheInput(
                    NumericTerm.ProductOf product)
                    ? new DecisionAtom.OfTheInput(product.standingWhereTheDeclarationsAdmit(declared))
                    : each.getKey();
            out.merge(atom, each.getValue(), (before, now) -> before.plus(now).orNull());
        }
        return new LinearForm<>(form.constant(), out);
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
