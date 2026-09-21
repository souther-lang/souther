package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.LinkedHashSet;
import java.util.Set;

/**
 * The declarations of modules that a body, once it is emitted, refers to by name.
 *
 * <p>What is asked is what the generated code needs to link against, and not what the source
 * mentions: a type that only annotates a binding is gone by then. A body that runs in a module
 * other than the one that declares it has to find each of these reachable from there.
 *
 * <p>Read off the tree as written, which is all there is for a body whose parameters take their
 * types from where it is called. What a typed body says is {@link CarriedBodyDependencies}', which
 * reads what the emitter reads and so also answers what only types decide, such as the enumeration a
 * comparison takes its order from. This lists the forms that name a class without a type: a
 * construction, a unit data written as a value, and a case a {@code match} tests against.
 *
 * <p>Either is the publishing module's early answer to a question the emitter settles. The emitter
 * names the class of a declared type at one place, {@code CodegenContext.cd}, and refuses to name one
 * the module it emits into cannot reach; what neither reading lists is refused there, as a fault of
 * the compiler and not of the author's code.
 */
public final class ExecutableDependencies {

    private ExecutableDependencies() {}

    /** Every type {@code body} constructs, reads the one value of, or tests a case against, in the
     * order it is met. */
    public static Set<TypeSymbol.AtModule> of(Hir.Expr body) {
        Set<TypeSymbol.AtModule> out = new LinkedHashSet<>();
        collect(body, out);
        return out;
    }

    private static void collect(Hir.Expr e, Set<TypeSymbol.AtModule> out) {
        if (e == null) {
            return;
        }
        if (e instanceof Hir.NewData built
                && built.typeName().answered() != null
                && built.typeName().answered().type() instanceof TypeSymbol.AtModule at) {
            out.add(at);
        }
        if (e instanceof Hir.Match match) {
            for (Hir.Case arm : match.cases()) {
                for (Hir.Name each : arm.caseTypes()) {
                    if (each.answered() != null
                            && each.answered().type() instanceof TypeSymbol.AtModule at) {
                        out.add(at);
                    }
                }
            }
        }
        if (e instanceof Hir.Var.Denoting named
                && named.denotes() instanceof ValueName.OfType unit
                && unit.type() instanceof TypeSymbol.AtModule at) {
            out.add(at);
        }
        Hir.forEachChild(e, child -> collect(child, out));
    }
}
