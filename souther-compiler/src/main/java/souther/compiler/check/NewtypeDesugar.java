package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * Lowers {@code 金額(500)} — a call whose name is a newtype — to the record literal
 * {@code 金額 { value = 500 }} ({@code Ast.NewData}) before type-checking and codegen. Doing it once
 * here means every later stage — the {@code typeOf} dispatch, the tail restriction, CTFE collection,
 * and the backend — sees only {@code NewData}, so the two spellings of a newtype construction get
 * identical treatment and no stage special-cases the call form (ADR-0032; the implicit field is
 * {@code value}, ADR-0014).
 *
 * <p>A module's fn bodies and its invariants are rewritten at different points, because they are
 * settled at different points: an invariant is spread, qualified and inlined before the bodies are,
 * so {@link #rewriteInvariants} runs where that settling ends and {@link #rewrite} runs one question
 * later. Both spellings reach every stage as a {@code NewData} either way, which is the property a
 * stage is written against.
 */
public final class NewtypeDesugar {
    private NewtypeDesugar() {}

    /** Rewrites every {@code Call(newtype, [arg])} in the module's fn bodies to a {@code NewData}. */
    public static Ast.Module rewrite(Ast.Module m, Symbols symbols) {
        List<Ast.FnDef> fns = new ArrayList<>();
        for (Ast.FnDef fn : m.fns()) {
            Ast.Expr body = fn.body() == null ? null : go(fn.body(), symbols);
            fns.add(new Ast.FnDef(fn.name(), fn.params(), fn.declaredReturn(), fn.intrinsicKey(),
                    body, fn.partial(), fn.pos()));
        }
        return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(),
                m.defs(), m.behaviors(), fns, m.examples(), m.fakes(), m.exampleFileTarget(), m.pos());
    }

    /**
     * Rewrites every {@code Call(newtype, [arg])} in each declaration's {@code invariant} to a
     * {@code NewData}. Run where the invariants are settled — after the helpers an invariant names
     * are expanded into it — so a construction written in a helper arrives here as the construction
     * it is, and every check over an invariant reads one spelling rather than two.
     */
    public static Ast.Module rewriteInvariants(Ast.Module m, Symbols symbols) {
        List<Ast.Def> defs = new ArrayList<>();
        for (Ast.Def def : m.defs()) {
            if (def instanceof Ast.Data d && !d.invariants().isEmpty()) {
                defs.add(new Ast.Data(d.name(), d.newtype(), d.includes(), d.fields(),
                        Ast.mapClauses(d.invariants(), inv -> go(inv, symbols)),
                        d.decoder(), d.encoder(), d.pos()));
            } else {
                defs.add(def);
            }
        }
        return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(),
                defs, m.behaviors(), m.fns(), m.examples(), m.fakes(), m.exampleFileTarget(), m.pos());
    }

    private static Ast.Expr go(Ast.Expr e, Symbols symbols) {
        return switch (e) {
            case Ast.Apply call -> {
                List<Ast.Expr> args = mapExprs(call.args(), symbols);
                // Whether this name is a type or something else was answered when the module's names
                // were resolved. Asking the type namespace again here would read a binding of the
                // same spelling as the type it shadows, and rewrite an application of it into a
                // construction — both of which compile, so the meaning would change in silence.
                TypeName built = call.denotes() instanceof ValueName.OfType named ? named.type() : null;
                if (built != null && symbols.get(built) instanceof Ast.Data nt && nt.newtype()) {
                    if (args.size() != 1) {
                        throw CompileException.of(
                                Diagnostic.of(null, "check.newtype.arity").title("check.arity.title")
                                        .at(call.pos(), call.fn().length()).args(call.fn(), args.size())
                                        .build(),
                                "`" + call.fn() + "` wraps one value, but is applied to " + args.size()
                                        + " argument(s)");
                    }
                    yield new Ast.NewData(
                            new Ast.Name(call.fn(), built, call.pos()),
                            List.of(new Ast.FieldInit("value", args.get(0), call.pos())),
                            List.of(), ConstructionOrigin.own(), call.pos());
                }
                yield new Ast.Apply(call.function(), args, call.origin(), call.pos());
            }
            case Ast.NewData nd -> {
                List<Ast.FieldInit> inits = new ArrayList<>();
                for (Ast.FieldInit fi : nd.inits()) {
                    inits.add(new Ast.FieldInit(fi.name(), go(fi.value(), symbols), fi.pos()));
                }
                yield new Ast.NewData(nd.typeName(), inits, nd.spreads(), nd.origin(), nd.pos());
            }
            case Ast.Neg neg -> new Ast.Neg(go(neg.operand(), symbols), neg.pos());
            case Ast.Binary bin ->
                    new Ast.Binary(bin.op(), go(bin.left(), symbols), go(bin.right(), symbols), bin.pos());
            case Ast.FieldAccess fa -> new Ast.FieldAccess(go(fa.target(), symbols), fa.field(), fa.pos());
            case Ast.ListLit lit -> new Ast.ListLit(mapExprs(lit.elements(), symbols), lit.pos());
            case Ast.ListComp comp ->
                    new Ast.ListComp(go(comp.element(), symbols), mapExprs(comp.guards(), symbols), comp.pos());
            case Ast.LetIn li ->
                    new Ast.LetIn(li.binder(), go(li.value(), symbols), li.declaredType(), li.annotated(), li.opens(),
                            go(li.body(), symbols), li.pos());
            case Ast.If iff ->
                    new Ast.If(go(iff.cond(), symbols), go(iff.then(), symbols), go(iff.els(), symbols), iff.pos());
            // the attempted construction is written `T(v)` too, so it is a Call until this rewrites it
            case Ast.IfConstructed ic ->
                    new Ast.IfConstructed(go(ic.construct(), symbols), ic.binder(),
                            go(ic.then(), symbols), arms(ic.els(), symbols), ic.pos());
            case Ast.Block b -> new Ast.Block(b.params(), go(b.body(), symbols), b.pos());
            case Ast.Tuple tup -> new Ast.Tuple(mapExprs(tup.elements(), symbols), tup.pos());
            case Ast.TupleGet tg -> new Ast.TupleGet(go(tg.tuple(), symbols), tg.index(), tg.arity(), tg.pos());
            case Ast.Match mt -> {
                List<Ast.Case> cases = new ArrayList<>();
                for (Ast.Case c : mt.cases()) {
                    cases.add(new Ast.Case(c.caseTypes(), c.binding(), go(c.body(), symbols),
                            c.unwrapAsserts(), c.pos()));
                }
                yield new Ast.Match(go(mt.scrutinee(), symbols), cases, mt.pos());
            }
            default -> e;   // literals, Var — no child expressions to rewrite
        };
    }

    private static List<Ast.Expr> mapExprs(List<Ast.Expr> es, Symbols symbols) {
        List<Ast.Expr> out = new ArrayList<>();
        for (Ast.Expr e : es) {
            out.add(go(e, symbols));
        }
        return out;
    }

    private static List<Ast.ElseArm> arms(List<Ast.ElseArm> arms, Symbols symbols) {
        List<Ast.ElseArm> out = new ArrayList<>();
        for (Ast.ElseArm arm : arms) {
            out.add(arm.with(go(arm.body(), symbols)));
        }
        return out;
    }
}
