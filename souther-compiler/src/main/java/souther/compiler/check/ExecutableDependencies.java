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
 * mentions: a type that only annotates a binding is gone by then, and a construction is a class the
 * emitted method has to name. A body that runs in a module other than the one that declares it has
 * to find each of these reachable from there.
 *
 * <p>Two forms of the tree name a class this way: a construction, and a unit data written as a
 * value, which is read from the class's shared instance. A form that emits a reference is added
 * here where it is found, and nothing that asks this needs to change.
 */
public final class ExecutableDependencies {

    private ExecutableDependencies() {}

    /** Every type {@code body} constructs or reads the one value of, in the order it is met. */
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
        if (e instanceof Hir.Var.Denoting named
                && named.denotes() instanceof ValueName.OfType unit
                && unit.type() instanceof TypeSymbol.AtModule at) {
            out.add(at);
        }
        Hir.forEachChild(e, child -> collect(child, out));
    }
}
