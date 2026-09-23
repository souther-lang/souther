package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * Lowers {@code 金額(500)} — a call whose name is a newtype — to the record literal
 * {@code 金額 { value = 500 }} ({@code Hir.NewData}) before type-checking and codegen. Doing it once
 * here means every later stage — the {@code typeOf} dispatch, the tail restriction, CTFE collection,
 * and the backend — sees only {@code NewData}, so the two spellings of a newtype construction get
 * identical treatment and no stage special-cases the call form (ADR-0032; the implicit field is
 * {@code value}, ADR-0014).
 *
 * <p>A module's fn bodies and its invariants are rewritten at different points, because they are
 * settled at different points: an invariant is spread, qualified and inlined before the bodies are,
 * so {@link #rewriteInvariantsOf} runs where that settling ends and {@link #rewriteOf} runs one
 * question later. Both spellings reach every stage as a {@code NewData} either way, which is the
 * property a stage is written against.
 */
public final class NewtypeDesugar {
    private NewtypeDesugar() {}

    /**
     * One definition's body, with each newtype construction written in it rewritten to the
     * construction it is.
     *
     * <p>A definition at a time, because an application that wraps no single value is wrong in the
     * body that wrote it and in no other. Rewriting them together answers for a whole module, and
     * one such application would leave every other definition without the form the check and the
     * backend read.
     */
    public static Hir.FnDef rewriteOf(Hir.FnDef fn, DeclarationNewtypes newtypes) {
        Hir.FnBody body = switch (fn.body()) {
            case Hir.FnBody.Written w -> new Hir.FnBody.Written(go(w.expr(), newtypes));
            case Hir.FnBody.Intrinsic i -> i;
        };
        return fn.withBody(body);
    }

    /**
     * One declaration's invariants, with each newtype construction written in them rewritten to the
     * construction it is. Run where the invariants are settled — after the helpers an invariant
     * names are expanded into it — so a construction written in a helper arrives here as the
     * construction it is, and every check over an invariant reads one spelling rather than two.
     *
     * <p>A declaration at a time, because what is wrong with one clause is wrong with the
     * declaration that wrote it and with nothing else. Rewriting them together would answer for a
     * whole module, and one bad application would leave every other declaration without the form
     * every later stage reads.
     */
    public static Hir.Def rewriteInvariantsOf(Hir.Def def, DeclarationNewtypes newtypes) {
        if (def instanceof Hir.Data d && !d.invariants().isEmpty()) {
            return new Hir.Data(d.written(), d.declares(), d.newtype(), d.includes(), d.fields(),
                    Hir.mapClauses(d.invariants(), inv -> rewriteInvariant(inv, newtypes)),
                    d.pos());
        }
        return def;
    }

    /**
     * One rule written in an invariant, rewritten the same way whether it is the whole clause or one
     * part of it.
     *
     * <p>Named rather than reached through a declaration, because a part of a clause is read
     * alongside the clause it is a part of and the two have to say the same thing about the same
     * text. Sent through the declaration instead, a part would have to be carried on a declaration
     * built to hold it, and would then take whatever else rewriting a declaration comes to mean.
     */
    public static Hir.Expr rewriteInvariant(Hir.Expr invariant, DeclarationNewtypes newtypes) {
        return go(invariant, newtypes);
    }

    private static Hir.Expr go(Hir.Expr e, DeclarationNewtypes newtypes) {
        return switch (e) {
            case Hir.Apply call -> {
                List<Hir.Expr> args = mapExprs(call.args(), newtypes);
                // Whether this name is a type or something else was answered when the module's names
                // were resolved. Asking the type namespace again here would read a binding of the
                // same spelling as the type it shadows, and rewrite an application of it into a
                // construction — both of which compile, so the meaning would change in silence.
                TypeSymbol built = call.answered() != null
                        && call.answered().denotes() instanceof ValueName.OfType named
                        ? named.type() : null;
                // The type name is the one the author applied, which a construction is named by. A
                // callee denoting a type is one they wrote, so this holds wherever the branch is
                // taken; asked of the callee it would be whatever a lowering had put there.
                // Whether the name was declared as a newtype, which was settled when its module was
                // indexed. Read off the declaration instead, a body writing `T(v)` for a `T` of
                // another module would be rewritten again whenever that declaration moved.
                if (built != null && call.applied().name() instanceof WrittenName wrote
                        && DeclarationFacts.isNewtype(built, newtypes) && args.size() == 1) {
                    // `T(v)` is what the author wrote and a construction is what it means, so the
                    // node that replaces the application stands over the same characters.
                    yield Hir.NewData.fromApply(call, new Hir.Name.Denoting(wrote, built),
                            List.of(new Hir.FieldInit("value", args.get(0), call.pos())));
                }
                yield call.withArgs(args);
            }
            case Hir.NewData nd -> {
                List<Hir.FieldInit> inits = new ArrayList<>();
                for (Hir.FieldInit fi : nd.inits()) {
                    inits.add(fi.withValue(go(fi.value(), newtypes)));
                }
                yield nd.with(inits, nd.spreads());
            }
            case Hir.Neg neg -> new Hir.Neg(go(neg.operand(), newtypes), neg.pos(), neg.region());
            case Hir.Binary bin ->
                    new Hir.Binary(bin.op(), go(bin.left(), newtypes), go(bin.right(), newtypes),
                            bin.origin(), bin.pos(), bin.region());
            case Hir.FieldAccess fa -> fa.withTarget(go(fa.target(), newtypes));
            case Hir.RowCollection row -> new Hir.RowCollection(mapExprs(row.elements(), newtypes),
                    row.origin(), row.pos(), row.region());
            case Hir.ListLit lit -> new Hir.ListLit(mapExprs(lit.elements(), newtypes), lit.origin(),
                    lit.pos(), lit.region());
            case Hir.ListComp comp ->
                    new Hir.ListComp(go(comp.element(), newtypes), mapExprs(comp.guards(), newtypes),
                            comp.origin(), comp.pos(),
                            comp.region());
            case Hir.LetIn li ->
                    new Hir.LetIn(li.binder(), go(li.value(), newtypes), li.declaredType(), li.annotated(), li.opens(),
                            go(li.body(), newtypes), li.pos(), li.region());
            // A construction written inside a helper is written `T(v)` there too, and reaches an
            // invariant already expanded. What `given` holds is inside the body as well, and is
            // rewritten there.
            case Hir.Expansion ex -> {
                List<Hir.Bound> bound = new ArrayList<>();
                for (Hir.Bound b : ex.bound()) {
                    bound.add(new Hir.Bound(b.binder(), b.declaredType(), go(b.value(), newtypes)));
                }
                yield new Hir.Expansion(ex.callee(), ex.application(), ex.at(), bound, ex.given(),
                        ex.declaredReturn(), go(ex.body(), newtypes), ex.pos(), ex.region());
            }
            case Hir.If iff ->
                    new Hir.If(go(iff.cond(), newtypes), go(iff.then(), newtypes), go(iff.els(), newtypes),
                            iff.origin(), iff.pos(), iff.region());
            // the attempted construction is written `T(v)` too, so it is a Call until this rewrites it
            case Hir.IfConstructed ic ->
                    new Hir.IfConstructed(go(ic.construct(), newtypes), ic.binder(),
                            go(ic.then(), newtypes), arms(ic.els(), newtypes), ic.origin(), ic.pos(),
                            ic.region());
            case Hir.Block b -> new Hir.Block(b.params(), go(b.body(), newtypes), b.rule(),
                    b.expandedFrom(), b.pos(),
                    b.region());
            case Hir.Tuple tup -> new Hir.Tuple(mapExprs(tup.elements(), newtypes), tup.pos(),
                    tup.region());
            case Hir.TupleGet tg -> new Hir.TupleGet(go(tg.tuple(), newtypes), tg.index(), tg.arity(),
                    tg.pos(), tg.region());
            case Hir.Match mt -> {
                List<Hir.Case> cases = new ArrayList<>();
                for (Hir.Case c : mt.cases()) {
                    cases.add(new Hir.Case(c.caseTypes(), c.binding(), go(c.body(), newtypes),
                            c.unwrapAsserts(), c.pos()));
                }
                yield new Hir.Match(go(mt.scrutinee(), newtypes), cases, mt.origin(), mt.pos(),
                        mt.region());
            }
            default -> e;   // literals, Var — no child expressions to rewrite
        };
    }

    private static List<Hir.Expr> mapExprs(List<Hir.Expr> es, DeclarationNewtypes newtypes) {
        List<Hir.Expr> out = new ArrayList<>();
        for (Hir.Expr e : es) {
            out.add(go(e, newtypes));
        }
        return out;
    }

    private static List<Hir.ElseArm> arms(List<Hir.ElseArm> arms, DeclarationNewtypes newtypes) {
        List<Hir.ElseArm> out = new ArrayList<>();
        for (Hir.ElseArm arm : arms) {
            out.add(arm.with(go(arm.body(), newtypes)));
        }
        return out;
    }
}
