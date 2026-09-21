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
 * <p>This is the publishing module's early answer to a question the emitter settles. The emitter
 * names the class of a declared type at one place, {@code CodegenContext.cd}, and refuses to name one
 * the module it emits into cannot reach. So a form of the tree that reaches that place is listed
 * here to be refused where the module is published; one that is not listed is refused at emission,
 * as a fault of the compiler and not of the author's code.
 *
 * <p>The forms that reach it: a construction, a unit data written as a value, and a case a
 * {@code match} tests against.
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
