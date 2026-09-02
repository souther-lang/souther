package souther.compiler.check;

import souther.compiler.semantics.ConditionJoin;
import souther.compiler.ast.Hir;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The clauses a module declares — a data's {@code invariant} and a behavior's {@code ensures} — with
 * the helpers they name expanded.
 *
 * <p>A clause is expanded well before a body is. An importer reads an included data's invariant
 * through the symbol table, so it has to be expanded by the time the table is built, and the settling
 * of the helper parameter types it reaches has to happen first — expanding a call carries the
 * parameter's type onto the binding the call becomes, so a type settled afterwards would never reach
 * the expansion. The two are done together here, in that order, and each caller says which of the two
 * representations it wants.
 *
 * <p>There are two, and they are read by different things. The settled form is what travels to an
 * importer and what the backend emits; the discharge form leaves the language's own operations
 * standing, because the analysis has rules about them ({@link InliningPolicy}).
 *
 * <p>Both kinds of clause are here because the expansion is one rule. What a helper call comes to
 * does not depend on whether the clause it stands in is written of a value or of an answer, and the
 * two representations are the same two either way.
 */
public final class ClauseHelpers {

    private ClauseHelpers() {}

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
    static Expansion<Hir.Module> withSettledInvariants(Hir.Module m, Symbols symbols,
                                                       Map<String, Hir.FnDef> published) {
        Hir.Module settled = settled(m, symbols);
        HelperInliner inliner = HelperInliner.forModule(settled, published, symbols.library());
        // What these expansions could not remove comes back with what they produced. A clause is the
        // one place a module writes an expression that is not a definition, so a recursion reached
        // from one is reached from nowhere a reader of the module's declarations would look.
        return new Expansion<>(withInlinedInvariants(inliner, settled), inliner.leftStanding());
    }

    /**
     * Each declaration's invariant in the representation the invariant-discharge analysis reads: the
     * helpers it can name expanded, the language's own operations left standing
     * ({@link InliningPolicy#DISCHARGE}), for every declaration {@code m} makes.
     *
     * <p>This is the same settling {@link #withSettledInvariants} does, stopped one step earlier, and
     * it reads the same table: what the clause names is substituted whether this module declared it or
     * imported it. What another module declares is not in here and is read in the settled form that
     * travels with it, which is where an imported clause falls outside the statically dischargeable
     * fragment (spec §invariant-discharge) — a rule {@link AnalysisInvariants} states off where the
     * declaration was written rather than off whether a lookup found anything.
     */
    public static AnalysisInvariants invariantsForDischarge(
            Expandable expandable, Symbols symbols, Map<String, Hir.FnDef> published) {
        Hir.Module m = expandable.module();
        Hir.Module settled = settled(m, symbols);
        HelperInliner inliner = HelperInliner.forHelpers(m.name(), HelperInliner.helpersOf(settled),
                published, InliningPolicy.DISCHARGE, symbols.library());
        Map<TypeSymbol.AtModule, List<Hir.InvariantClause>> out = new LinkedHashMap<>();
        // Every declaration this module makes, and not the ones with something to say. What is
        // filed for a declaration is its reading, and a declaration whose reading is nothing has
        // one — so an absent entry is this module's reading having failed to arrive rather than a
        // declaration that wrote no clause, which is the difference {@link AnalysisInvariants}
        // rests on.
        for (Hir.Def def : settled.defs()) {
            if (def instanceof Hir.Data d) {
                TypeSymbol.AtModule declared = d.declares();
                out.put(declared, Hir.mapClauses(d.invariants(),
                        clause -> inliner.inline(clause, new BindingOwner.OfData(declared))));
            }
        }
        return new AnalysisInvariants(m.name(), out);
    }

    /** {@code m} with its helper parameter types settled and the names in its invariants written
     * qualified — what both representations are expanded from, so neither reads a table the other
     * would key differently. */
    static Hir.Module settled(Hir.Module m, Symbols symbols) {
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
                        d.pos()));
            } else {
                defs.add(def);
            }
        }
        List<Hir.BehaviorDef> behaviors = new ArrayList<>();
        for (Hir.BehaviorDef behavior : m.behaviors()) {
            behaviors.add(behavior instanceof Hir.SpecBehavior spec && !spec.ensures().isEmpty()
                    ? withInlinedEnsures(inliner, m.name(), spec) : behavior);
        }
        return m.withDefs(defs).withBehaviors(behaviors);
    }

    /** {@code spec} with the helper calls in its {@code ensures} expanded as {@code inliner} expands
     * them — which representation that leaves is the inliner's to say, and the same walk gives
     * either. */
    private static Hir.SpecBehavior withInlinedEnsures(HelperInliner inliner, String module,
                                                       Hir.SpecBehavior spec) {
        BindingOwner owner = new BindingOwner.OfSignature(
                new souther.compiler.types.ValueName.Behavior(module, spec.name()));
        List<Hir.EnsuresClause> clauses = new ArrayList<>();
        for (Hir.EnsuresClause clause : spec.ensures()) {
            List<Hir.EnsuresArm> arms = new ArrayList<>();
            for (Hir.EnsuresArm arm : clause.arms()) {
                arms.add(arm.with(inliner.inline(arm.expr(), owner)));
            }
            clauses.add(new Hir.EnsuresClause(clause.name(), List.copyOf(arms),
                    clause.pos(), clause.region()));
        }
        return new Hir.SpecBehavior(spec.written(), spec.params(), spec.ret(),
                spec.constructs(), spec.dependsOn(), List.copyOf(clauses), spec.pos());
    }

    /**
     * Where a written clause begins: the earliest position anything in it carries.
     *
     * <p>A node's own position is where its operator is written, so the position of {@code a && b} is
     * the {@code &&}. A reader is pointed at the clause, which starts at whatever of it comes first.
     *
     * <p>Of what was written. Asked of an expanded tree it answers with a position inside whatever
     * was expanded into it, which is why the reader that wants both this and the expansion gets them
     * made together ({@link ClausesForDischarge}).
     */
    static SourcePos beginsAt(Hir.Expr e) {
        SourcePos[] found = {e.pos()};
        Hir.forEachChild(e, child -> {
            SourcePos inner = beginsAt(child);
            if (inner != null && (found[0] == null || earlier(inner, found[0]))) {
                found[0] = inner;
            }
        });
        return found[0];
    }

    private static boolean earlier(SourcePos a, SourcePos b) {
        return a.line() != b.line() ? a.line() < b.line() : a.column() < b.column();
    }

    /** The conjuncts of a clause, flattened, in the order they are written — what a reader sees as
     * separate clauses. */
    public static List<Hir.Expr> conjunctsOf(Hir.Expr e) {
        if (e instanceof Hir.Binary b
                && ConditionJoin.of(b.op()).orElse(null) == ConditionJoin.BOTH) {
            List<Hir.Expr> out = new ArrayList<>(conjunctsOf(b.left()));
            out.addAll(conjunctsOf(b.right()));
            return out;
        }
        return List.of(e);
    }
}
