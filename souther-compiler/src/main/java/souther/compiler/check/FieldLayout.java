package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * The order a value of a declaration lays its fields out in: what each spread brings in, spread by
 * spread as they are written, and then what the declaration writes itself.
 *
 * <p><b>A sequence, and it is the whole of what this says.</b> Which is what {@link
 * EffectiveFieldTypes} cannot say and does not: two of those holding the same names for the same
 * types are one answer however the fields are written, so a reader taking the order off one would
 * be reading something no edit to that order will ever wake it about. Asked here, the order is the
 * answer, and a declaration whose fields are written the other way round is a different one.
 *
 * <p>Beside {@link EffectiveFieldTypes} and not joined to it, for the reason the bindings are
 * beside it too: what a field holds and where a field stands move at different times, and a reader
 * of the one has no business being worked out again by an edit to the other.
 *
 * <p>What this decides is what a constructor of the type takes and in what order, what a value
 * written out is read back in, and the order a construction's values are handed over in. One
 * answer for all of them, so that what the check lines a construction up against and what the
 * backend emits it as cannot come apart.
 *
 * <p>Empty where the declaration reaches no field — a sum, a unit data, or a spread of something
 * that is not a product.
 */
@FunctionalInterface
public interface FieldLayout {

    /** The names of the fields {@code declared} reaches, in the order a value lays them out. */
    List<String> of(TypeSymbol.AtModule declared);

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    FieldLayout NONE = _ -> List.of();

    /**
     * The same expansion over the declarations in {@code symbols}.
     *
     * <p>For a reading that has not been handed the compilation's answer. What a spread brings in
     * and in what order is decided by {@link FieldExpansion}, which both worlds read, so a reading
     * made here and one made from the store lay a value out alike.
     */
    static FieldLayout asWritten(Symbols symbols) {
        return declared -> symbols.declaredNode(declared) instanceof Hir.Data data
                ? TypeOps.fieldLayout(data, symbols) : List.of();
    }
}
