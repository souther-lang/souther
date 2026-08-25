package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.core.ValueShape;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * What a value of a declared data is made of and what must hold of one, elaborated once.
 *
 * <p>The reading that runs. A clause used to be typed here and elaborated again by whatever ran it,
 * which put the last step of deciding what a clause means inside a backend (issue #81, ADR-0021);
 * what comes out of here is what the check holds the clause to and what a construction is refused
 * by.
 *
 * <p>Every clause that applies, and not the ones this declaration wrote. An include carries the
 * clauses of what it takes in, and they are checked where the value is built — over the fields that
 * data has, each read through the binding the declaration that wrote it gave
 * ({@link TypeOps#fieldBindings}). So the unit is the data being built and not the declaration a
 * clause was written on: an answer keyed by where a clause was written would be short exactly the
 * clauses a construction has to satisfy.
 */
public final class ExecutableInvariants {

    private ExecutableInvariants() {}

    /**
     * {@code data} as it is built and checked.
     *
     * @param helpers the signatures of the recursive helpers a clause may reach — the same table the
     *     body check reads, because a clause naming a total helper names the same one a body does
     * @throws CompileException where a clause is not a condition
     */
    public static ValueShape of(Hir.Data data, Symbols symbols, Map<String, Type> helpers) {
        Map<String, Type> types = TypeOps.fieldTypes(data, symbols);
        Map<String, BindingId> bindings =
                TypeOps.fieldBindings(data.declares(), data, symbols);
        List<ValueShape.Field> fields = new ArrayList<>();
        // In the order a value lays its fields out, which is what `fieldTypes` answers. The bindings
        // are a walk of their own and answer in an order of nothing's deciding, so what is read off
        // them is the binding of a field this one named.
        types.forEach((field, type) -> fields.add(
                new ValueShape.Field(field, type, bindings.get(field))));

        Scope reading = DataChecker.fieldScope(data.declares(), data, symbols).reaching(helpers);
        CheckContext ctx = CheckContext.executableInvariant(symbols, data);
        List<ValueShape.Invariant> invariants = new ArrayList<>();
        for (Hir.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
            // Desugared first, the way a body is: a clause writing a comprehension states the same
            // condition as the `if` it is derived from, and one of the two reaching the check and
            // the other reaching what runs is the shape this exists to stop.
            Core condition = Elaborator.elaborate(Lower.desugarExpr(clause.expr()), reading, ctx);
            if (condition.type() != Type.BOOL) {
                throw CompileException.of(Diagnostic.at(clause.expr().pos())
                        .say(new DeclarationMessage.AnInvariantExpressionIsBool(
                                Type.show(condition.type()))).build());
            }
            invariants.add(new ValueShape.Invariant(clause.name(), condition));
        }
        return new ValueShape(data.declares(), fields, invariants);
    }
}
