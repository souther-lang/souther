package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.derive.Deriver;
import souther.compiler.diag.CompileException;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;

/**
 * An expandable module whose declarations have the invariants of every type they spread settled into
 * them, with the codecs those declarations need derived along the way.
 *
 * <p>The name is the part a reader cannot see for itself. A derived codec is in the tree — a
 * decoder node is there or it is not — and an invariant that arrived by spread is not: it reads like
 * one the declaration wrote, and what this says is that nothing is left to follow back to the type
 * it was spread from. A pass that read a declaration before this would read the same shape meaning
 * something weaker.
 *
 * <p>{@link #settle} owns the rewrites rather than taking their result. Handed a finished tree
 * instead, this would be somewhere to make the claim about anything — which is what a wrapper with a
 * {@code with} operation is, and what the claim being carried by nothing looked like the first time.
 * The two go together in one step because the settling reads the spread source through the symbols
 * the derive produced.
 *
 * <p>What it hands out is what its consumers ask of it: the declarations, the definitions, and the
 * tree with each declaration replaced by what that declaration came to. Not the tree itself — a
 * reader holding that holds a module whose invariants look settled and is no longer being told that
 * they are.
 */
public final class InvariantSettled {

    private final Hir.Module module;

    private InvariantSettled(Hir.Module module) {
        this.module = module;
    }

    /**
     * {@code expandable} with its codecs derived and its spread invariants settled.
     *
     * <p>{@code published} is what the modules this one imports offer it: an invariant names what is
     * in scope where it is written, and an imported definition is in scope there as it is in a body.
     *
     * @throws CompileException where a declaration of the module cannot be derived or a clause it
     *     spreads cannot be read
     */
    public static InvariantSettled settle(Expandable expandable, Symbols scope,
                                          Map<String, Hir.FnDef> published) {
        Hir.Module declared = onlyWhatItDeclares(expandable.module());
        Hir.Module derived = Deriver.derive(declared, scope);
        return new InvariantSettled(
                HelperInvariants.withSettledInvariants(derived, scope, published));
    }

    /**
     * The module carrying only the declarations it may have. A name written twice keeps the first,
     * reported where declarations are indexed; the second is not a declaration, so nothing below
     * here should read it and find it disagreeing with the one that is.
     *
     * <p>Which those are is {@link TypeChecker#declared}'s to say, and it says it once — asking it
     * again here rather than repeating the rule is what keeps the tree and the scope agreeing about
     * what the module declares.
     */
    private static Hir.Module onlyWhatItDeclares(Hir.Module m) {
        Collection<Hir.Def> kept = TypeChecker.declared(m).defs().values();
        if (kept.size() == m.defs().size()) {
            return m;
        }
        return new Hir.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(),
                List.copyOf(kept), m.behaviors(), m.fns(), m.takenOn(), m.examples(), m.fakes(),
                m.exampleFileTarget(), m.pos());
    }

    /** What the module is called. */
    public String name() {
        return module.name();
    }

    /** Its declarations, each with its invariants settled. */
    public List<Hir.Def> defs() {
        return module.defs();
    }

    /** Its definitions, as resolution left them. */
    public List<Hir.FnDef> fns() {
        return module.fns();
    }

    /**
     * The tree with each declaration replaced by the one of {@code derived} that answers to its
     * name, or null where one of them has no answer.
     *
     * <p>An assembly, and what it answers with is a tree and not a state of this module: what each
     * declaration came to is that declaration's answer, and a module put back together from them
     * claims nothing this carrier claims.
     */
    public Hir.Module withEachDeclarationDerived(Map<String, Hir.Def> derived) {
        List<Hir.Def> defs = new ArrayList<>();
        for (Hir.Def def : module.defs()) {
            Hir.Def came = derived.get(def.name());
            if (came == null) {
                return null;
            }
            defs.add(came);
        }
        return new Hir.Module(module.name(), module.exposing(), module.exposedOutputs(),
                module.imports(), defs, module.behaviors(), module.fns(), module.takenOn(),
                module.examples(), module.fakes(), module.exampleFileTarget(), module.pos());
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof InvariantSettled other && module.equals(other.module);
    }

    @Override
    public int hashCode() {
        return module.hashCode();
    }

    @Override
    public String toString() {
        return module.toString();
    }
}
