package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

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

    /**
     * The application is the one kind this pass reads. Every other kind is rebuilt around its
     * rewritten children by {@link Hir#mapChildren}, which is where a node kind added to {@code Hir}
     * is refused until someone says what its slots are. That includes an {@code Expansion}, whose
     * {@code given} is inside its body as well and is rewritten there.
     */
    private static Hir.Expr go(Hir.Expr e, DeclarationNewtypes newtypes) {
        if (!(e instanceof Hir.Apply call)) {
            return Hir.mapChildren(e, child -> go(child, newtypes), name -> name);
        }
        Hir.Apply rewritten = call.mapArgs(arg -> go(arg, newtypes));
        List<Hir.Expr> args = rewritten.args();
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
            return Hir.NewData.fromApply(call, new Hir.Name.Denoting(wrote, built),
                    List.of(new Hir.FieldInit("value", args.get(0), call.pos())));
        }
        return rewritten;
    }
}
