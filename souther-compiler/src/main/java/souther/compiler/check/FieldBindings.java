package souther.compiler.check;

import souther.compiler.types.BindingId;
import souther.compiler.types.TypeSymbol;

import java.util.Map;

/**
 * Which binding each of a declaration's effective fields is, for a reader of what its clauses state.
 *
 * <p>One answer and not a field at a time. What a clause of a declaration reads resolves against the
 * fields that declaration reaches — its own and the ones its spreads bring in — and a field brought
 * in keeps the binding of the declaration that wrote it, because the clause that reads it was written
 * there too. So the answer is the closure a walk from one declaration makes, settled by reading a
 * declaration's own fields before the ones its spreads bring in: the nearer binding is the one a
 * name means.
 *
 * <p><b>A mapping, and that precedence is not an order it answers.</b> Reading the nearer first is
 * how a name is settled, not a sequence anything may take off the result — and it could not be the
 * order a value lays its fields out in, which takes in what is spread before what is written. A
 * reader of that asks {@link FieldLayout}.
 *
 * <p><b>Bindings and not types.</b> A field's type changing leaves every binding where it was.
 * Answered together with what each field holds, a reader of the bindings would be worked out again
 * by an edit that only changed a type — which is the same over-reading a declaration's meaning was
 * cut apart to stop.
 *
 * <p>Beside {@link Symbols} rather than on it. A carrier of declarations answers what a declaration
 * is; this says what a walk over several of them came to, which is not something one declaration
 * holds.
 */
@FunctionalInterface
public interface FieldBindings {

    /**
     * Which binding each field {@code declared} reaches is, empty where it declares no fields.
     *
     * <p>Asked of the declaration as the reader reached it, which is what the bindings are owned by:
     * a field is bound under the declaration that wrote it, and the clause that reads it resolves
     * against that same name.
     */
    Map<String, BindingId> of(TypeSymbol.AtModule declared);

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    FieldBindings NONE = _ -> Map.of();

    /**
     * The same walk over the declarations in {@code symbols}.
     *
     * <p>For a reading that has not been handed the compilation's answer. The walk is
     * {@link TypeOps#fieldBindings}, which owns it: what an include reaches and which declaration
     * binds a field it brought in is decided there and nowhere else.
     */
    static FieldBindings asWritten(Symbols symbols) {
        return declared -> TypeOps.fieldBindings(declared, symbols);
    }
}
