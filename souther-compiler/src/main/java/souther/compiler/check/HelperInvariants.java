package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A declaration's {@code invariant} with the helpers it names expanded.
 *
 * <p>An invariant is expanded well before a body is. An importer reads an included data's invariant
 * through the symbol table, so it has to be expanded by the time the table is built, and the settling
 * of the helper parameter types it reaches has to happen first — expanding a call carries the
 * parameter's type onto the binding the call becomes, so a type settled afterwards would never reach
 * the expansion. The two are done together here, in that order, and each caller says which of the two
 * representations it wants.
 *
 * <p>There are two, and they are read by different things. The settled form is what travels to an
 * importer and what the backend emits; the discharge form leaves the language's own operations
 * standing, because the analysis has rules about them ({@link InliningPolicy}).
 */
public final class HelperInvariants {

    private HelperInvariants() {}

    /**
     * Settles the helper parameter types the author left unwritten, then inlines the helper calls in
     * every data's {@code invariant}.
     *
     * <p>The settling is done here as well as in {@link Lower}, and is idempotent: a parameter already
     * typed is left alone, and {@code Lower} settles what only the fully desugared module can
     * determine.
     *
     * <p>An invariant is pure and cannot call an injected behavior (spec §invariant-expressions), so
     * nothing here needs the injected signatures to settle the helpers an invariant reaches.
     *
     * <p>{@code published} is what the modules this one imports offer it. An invariant names what is
     * in scope where it is written, and an imported definition is in scope there as it is in a body; it
     * is substituted here for the reason a body's is, so what the invariant carries afterwards names
     * nothing of the module that declared it. The names are written qualified first, because that is
     * the spelling the table is keyed by — {@link HelperNames#qualifyImports} does it again for the
     * bodies below, and says the same thing both times.
     */
    static Hir.Module withSettledInvariants(Hir.Module m, Symbols symbols,
                                            Map<String, Hir.FnDef> published) {
        Hir.Module settled = settled(m, symbols);
        return withInlinedInvariants(HelperInliner.forModule(settled, published), settled);
    }

    /**
     * Each declaration's invariant in the representation the invariant-discharge analysis reads: the
     * helpers it can name expanded, the language's own operations left standing
     * ({@link InliningPolicy#DISCHARGE}). Keyed by the declaration's name in {@code m}.
     *
     * <p>This is the same settling {@link #withSettledInvariants} does, stopped one step earlier, and
     * it reads the same table: what the clause names is substituted whether this module declared it or
     * imported it. An importer reads an imported invariant in the settled form and finds nothing here
     * for it, which is where an imported clause falls outside the statically dischargeable fragment
     * (spec §invariant-discharge).
     */
    public static Map<TypeSymbol, List<Hir.InvariantClause>> invariantsForDischarge(
            Expandable expandable, Symbols symbols, Map<String, Hir.FnDef> published) {
        Hir.Module m = expandable.module();
        Hir.Module settled = settled(m, symbols);
        HelperInliner inliner = HelperInliner.forHelpers(m.name(), HelperInliner.helpersOf(settled),
                published, InliningPolicy.DISCHARGE);
        Map<TypeSymbol, List<Hir.InvariantClause>> out = new LinkedHashMap<>();
        for (Hir.Def def : settled.defs()) {
            if (def instanceof Hir.Data d && !d.invariants().isEmpty()) {
                TypeSymbol declared = d.declares();
                out.put(declared, Hir.mapClauses(d.invariants(),
                        clause -> inliner.inline(clause, new BindingOwner.OfData(declared))));
            }
        }
        return out;
    }

    /** {@code m} with its helper parameter types settled and the names in its invariants written
     * qualified — what both representations are expanded from, so neither reads a table the other
     * would key differently. */
    private static Hir.Module settled(Hir.Module m, Symbols symbols) {
        return HelperNames.withQualifiedInvariants(HelperParams.settle(m, symbols, Map.of()));
    }

    /**
     * Inlines helper calls inside every data's {@code invariant}, so a rule named with a {@code let}
     * (e.g. {@code invariant 正の数(value)}) expands to its body before the invariant is type-checked
     * or emitted — the same lowering a behavior body gets (spec §blocks, §invariant-expressions).
     */
    private static Hir.Module withInlinedInvariants(HelperInliner inliner, Hir.Module m) {
        List<Hir.Def> defs = new ArrayList<>();
        for (Hir.Def def : m.defs()) {
            if (def instanceof Hir.Data d && !d.invariants().isEmpty()) {
                BindingOwner declared = new BindingOwner.OfData(d.declares());
                defs.add(new Hir.Data(d.written(), d.declares(), d.newtype(), d.includes(), d.fields(),
                        Hir.mapClauses(d.invariants(), clause -> inliner.inline(clause, declared)),
                        d.decoder(), d.encoder(), d.pos()));
            } else {
                defs.add(def);
            }
        }
        return new Hir.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(),
                defs, m.behaviors(), m.fns(), m.takenOn(), m.examples(), m.fakes(),
                m.exampleFileTarget(), m.pos());
    }

    /** The conjuncts of an invariant expression, flattened, in the order they are written — what a
     * reader sees as separate clauses. */
    public static List<Hir.Expr> conjunctsOf(Hir.Expr e) {
        if (e instanceof Hir.Binary b && b.op() == Hir.BinOp.AND) {
            List<Hir.Expr> out = new ArrayList<>(conjunctsOf(b.left()));
            out.addAll(conjunctsOf(b.right()));
            return out;
        }
        return List.of(e);
    }
}
