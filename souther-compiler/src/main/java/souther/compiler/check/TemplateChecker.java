package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.Map;

/**
 * Types the template of a value: what it means, as the analysis reads it.
 *
 * <p>Asked once for a value and not once for every body that builds it. A value takes nothing and
 * names nothing of where it is built, so what is typed here is the same whichever behavior asked,
 * and a module in which many behaviors build one value would otherwise type it as many times.
 *
 * <p>In a scope of its own: no name of a behavior's inputs is in force in it, and the recursive
 * helpers the value reaches are the ones it is handed.
 */
public final class TemplateChecker {

    private TemplateChecker() { }

    /**
     * The template {@code body} is, typed.
     *
     * @param body               the value's body as the analysis expands it
     * @param declared           the type the value declares, which its body is typed against as
     *                           the value's own check types it, or null where it declares none
     * @param elements           what its expansion said of the elements of the bindings it writes
     * @param recursiveHelperFns the recursive helpers the value calls, by their signatures
     * @param settledValues      what each value of the module was settled as, which is what a build
     *                           of one inside this value is typed by
     */
    public static InvariantChecker.Template check(
            Hir.Expr body, Type declared, ElementProvenance elements, Symbols symbols,
            DeclarationAccess declarations,
            Map<ValueName.Behavior, ReqSig> reqSigs, Map<String, Type> recursiveHelperFns,
            Preserved.SettledValues settledValues) {
        CheckContext context =
                new CheckContext(symbols, declarations, null, reqSigs)
                        .forDischarge(settledValues);
        Core typed = Elaborator.elaborate(body, Scope.NONE.reaching(recursiveHelperFns), context,
                declared);
        return new InvariantChecker.Template(typed, elements);
    }
}
