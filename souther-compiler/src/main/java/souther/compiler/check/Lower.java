package souther.compiler.check;

import souther.compiler.ast.Ast;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The Lower stage (ADR-0021): rewrites the surface AST toward the form the backend emits, so the
 * backend only emits and never rewrites. It runs before the type checker, whose body check consumes
 * the lowered form (a behavior's permission and {@code depends on} are defined on the inlined body,
 * spec 12.5).
 *
 * <p>It inlines every behavior-implementing {@code fn} body once (spec 12.5) and desugars the
 * body-level constructs that have a plain-AST equivalent — currently the guard-only list
 * comprehension {@code [e | g]}, which becomes {@code if g then [e] else []}. The backend then
 * emits from the lowered module instead of re-running the inliner or shaping these constructs
 * itself, and the type checker's body check consumes the same lowered form. Helper fns are left
 * untouched — they are inlined at their call sites, so a comprehension inside one is desugared once
 * it lands in a behavior body. Later slices grow this stage into a typed Core IR and move the
 * remaining backend-side rewrites (fold shaping, {@code match} lowering, closure conversion) here.
 */
public final class Lower {

    private Lower() {}

    /**
     * The two trees this stage answers with: the surface module it settled helper parameter types on,
     * and the lowered module the backend emits from. The type check reads both — the surface one for
     * the declarations, the lowered one for the bodies — so they must be the same settling, which is
     * why they are handed back together rather than settled again downstream.
     */
    public record Lowered(Ast.Module settled, Ast.Module lowered) {}

    /**
     * {@code module} with every helper parameter the author left unwritten carrying the type its body
     * gives it.
     *
     * <p>Settling comes before the expansion because inlining is what carries a parameter's type onto
     * the binding a call becomes (issue #178): a type settled afterwards would never reach it.
     */
    public static Ast.Module settle(Ast.Module module, Symbols symbols,
                                    Map<String, ReqSig> reqSigs) {
        return HelperParams.settle(module, symbols, reqSigs);
    }

    /**
     * One fn as the backend emits it: its helper calls expanded and its comprehensions desugared.
     *
     * <p>A behavior body and a recursive helper both survive to the backend this way — non-recursive
     * calls expanded, recursive calls left standing (spec 13.1). A recursive helper expands its own
     * body with its parameters hidden from helper resolution ({@code foldFrom}'s {@code step} is a
     * parameter, not a same-named user helper), which is what {@code recursive} says. A helper that is
     * neither is fully inlined at its call sites and never emitted, so nothing asks for it here.
     */
    public static Ast.FnDef body(Ast.FnDef fn, HelperInliner inliner, boolean recursive) {
        return body(fn, inliner, recursive, Set.of());
    }

    /**
     * The same, for a behavior's implementation, told what its behavior declares in {@code depends
     * on} — the names that arrive as the {@code let}'s trailing parameters (spec §depends-on). A
     * helper has none, and neither has a recursive helper's own body.
     */
    public static Ast.FnDef body(Ast.FnDef fn, HelperInliner inliner, boolean recursive,
                                 Set<String> dependencies) {
        Ast.Expr expanded = recursive
                ? inliner.inlineRecursiveBody(fn) : inliner.inline(fn.body(), dependencies);
        return new Ast.FnDef(fn.name(), fn.params(), fn.declaredReturn(), fn.intrinsicKey(),
                desugar(expanded), fn.partial(), fn.pos());
    }

    /** {@code module} with {@code fns} as its fns and every data invariant desugared — the tree the
     * backend emits from. */
    public static Ast.Module lowered(Ast.Module module, List<Ast.FnDef> fns) {
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.Data d && !d.invariants().isEmpty()) {
                defs.add(new Ast.Data(d.name(), d.newtype(), d.includes(), d.fields(),
                        Ast.mapClauses(d.invariants(), Lower::desugar),
                        d.decoder(), d.encoder(), d.pos()));
            } else {
                defs.add(def);
            }
        }
        return new Ast.Module(module.name(), module.exposing(), module.exposedOutputs(),
                module.imports(), defs, module.behaviors(), fns,
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

    /** Desugars one expression the way a body is desugared, for the paths that hold a single
     * expression rather than a module: the codec emitters, whose decoders and encoders are still
     * AST-level, run their expressions through this before they are typed and emitted. */
    public static Ast.Expr desugarExpr(Ast.Expr e) {
        return desugar(e);
    }

    /** Post-order rewrite: desugar the children first, then the node itself if it is a comprehension. */
    private static Ast.Expr desugar(Ast.Expr e) {
        Ast.Expr mapped = Ast.mapChildren(e, Lower::desugar);
        return mapped instanceof Ast.ListComp comp ? listCompToIf(comp) : mapped;
    }

    /**
     * {@code [element | g1, g2]} is {@code if g1 then (if g2 then [element] else []) else []}: the
     * element is included exactly when every guard holds, giving a 0-or-1 element list (spec 18.4).
     * The guards nest rather than joining with {@code &&} so a later guard is not evaluated once an
     * earlier one is false — {@code &&} evaluates both sides (spec 18.1), which would run (and could
     * abort in) a guard the original comprehension short-circuited past.
     */
    private static Ast.Expr listCompToIf(Ast.ListComp comp) {
        Ast.Expr result = new Ast.ListLit(List.of(comp.element()), comp.pos());
        List<Ast.Expr> guards = comp.guards();
        for (int i = guards.size() - 1; i >= 0; i--) {
            result = new Ast.If(guards.get(i), result, new Ast.ListLit(List.of(), comp.pos()), comp.pos());
        }
        return result;
    }
}
