package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.derive.Deriver;
import souther.compiler.diag.CompileException;
import souther.compiler.types.TypeKey;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * An expandable module whose invariants say what they say — every clause is the rule it states,
 * rather than a call to a helper that states it or a name that means something elsewhere.
 *
 * <p>What is settled, exactly:
 *
 * <ul>
 *   <li>a clause naming a helper carries that helper's body, so a reader has the rule and not a
 *       call it would have to expand to find out;</li>
 *   <li>a name in a clause that denotes another module's definition is written qualified, which is
 *       the spelling every table that reads a clause is keyed by;</li>
 *   <li>a helper's parameter types are settled, since a clause is read through them;</li>
 *   <li>the codecs the declarations need are derived, which the settling reads through.</li>
 * </ul>
 *
 * <p>What is <em>not</em> settled is what a declaration takes in by a spread. A clause of the type
 * spread from is still that type's, and which clauses apply to a declaration is composed on demand
 * by {@link TypeOps#declaredInvariants} walking {@code includes()}. A reader that took this state to
 * mean the spreads had been flattened into each declaration would find a declaration's own clauses
 * where it expected every clause that governs it.
 *
 * <p>The name is the part a reader cannot see for itself. A derived codec is in the tree — a decoder
 * node is there or it is not — and a clause that has been expanded is not: it reads like one the
 * author wrote that way, and what this says is that nothing in it is left to expand. A pass that
 * read a declaration before this would read the same shape meaning something weaker.
 *
 * <p>{@link #settle} owns the rewrites rather than taking their result. Handed a finished tree
 * instead, this would be somewhere to make the claim about anything — which is what a wrapper with a
 * {@code with} operation is, and what the claim being carried by nothing looked like the first time.
 * The derive and the settling go together in one step because a clause is expanded through the
 * symbols the derive produced.
 *
 * <p>What it hands out is what its consumers ask of it: the declarations, the definitions, and the
 * tree with each declaration replaced by what that declaration came to. Not the tree itself — a
 * reader holding that holds a module whose invariants look settled and is no longer being told that
 * they are.
 */
public final class InvariantSettled {

    private final Hir.Module module;
    private final java.util.SequencedSet<souther.compiler.types.ReachName.Declaration> standing;

    private InvariantSettled(Expansion<Hir.Module> expanded) {
        this.module = expanded.value();
        this.standing = expanded.standing();
    }

    /**
     * {@code expandable} with its codecs derived and its clauses expanded.
     *
     * <p>{@code published} is what the modules this one imports offer it: an invariant names what is
     * in scope where it is written, and an imported definition is in scope there as it is in a body.
     *
     * @throws CompileException where a declaration of the module cannot be derived or a clause it
     *     spreads cannot be read
     */
    public static InvariantSettled settle(Expandable expandable, Symbols scope,
                                          Map<String, Hir.FnDef> published) {
        Hir.Module derived = Deriver.derive(expandable.module(), scope);
        return new InvariantSettled(
                ClauseHelpers.withSettledInvariants(derived, scope, published));
    }

    /**
     * Every recursive helper the clauses of this module left a call to standing.
     *
     * <p>A module's declarations are in the table a call graph is built over, so what one of their
     * bodies reaches is answered by following edges. A clause is not a declaration and is in no
     * table, so what it reaches is known only to the expansion that read it — which is here, and is
     * why this travels with the settled module rather than being looked for again afterwards.
     */
    public java.util.SequencedSet<souther.compiler.types.ReachName.Declaration> standingRecursiveCalls() {
        return standing;
    }


    /** What the module is called. */
    public String name() {
        return module.name();
    }

    /** The tree, for the states of this package that are assembled from it. */
    Hir.Module module() {
        return module;
    }

    /**
     * Its declarations, each of them the settled declaration and not the node.
     *
     * <p>The whole of the way to one, so a reader that has a declaration of this module has what
     * this state says about it. Handing over {@link Hir.Def} instead would put the module-level
     * claim back where it was — carried by nobody — one level down: the pass that reads a
     * declaration's clauses does different work depending on whether they have been expanded, and
     * silently.
     */
    public List<Def> defs() {
        List<Def> out = new ArrayList<>();
        for (Hir.Def def : module.defs()) {
            out.add(new Def(def));
        }
        return out;
    }

    /**
     * Its definitions, as resolution left them but for the helper parameter types this settled.
     *
     * <p>Handed over as they are, because nothing this state claims is about them. What reads a
     * definition here rewrites the newtype constructions in its body, and that reading is the same
     * whether or not anything has been settled — measured, not assumed. What does depend on the
     * settling is further down, where a helper's parameter type is read, and that is the fn family's
     * to carry when it has one.
     */
    public List<Hir.FnDef> fns() {
        return module.fns();
    }

    /**
     * One declaration of a settled module.
     *
     * <p>Its own type because a reader of one needs what the module-level state says: a clause here
     * is the rule it states. {@code NewtypeDesugar.rewriteInvariantsOf} is the measured case — handed
     * a declaration whose clause still names a helper, it rewrites the constructions it can see,
     * which are none of the ones in the helper's body, and says nothing about it.
     *
     * <p>Reached from the module and from nothing else. A way to make one out of a node would be
     * the module-level {@code with} written one level down.
     */
    public static final class Def {

        private final Hir.Def def;

        private Def(Hir.Def def) {
            this.def = def;
        }

        /** The name it is declared under. */
        public String name() {
            return def.name();
        }

        /** Which declaration it is. */
        public TypeKey declaredKey() {
            return def.declaredKey();
        }

        /** The node, for the passes of this package that read one. */
        Hir.Def def() {
            return def;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Def other && def.equals(other.def);
        }

        @Override
        public int hashCode() {
            return def.hashCode();
        }
    }

    /**
     * Both of what this answers with. The standing set is not derived from the tree by anything that
     * reads this — it is what the expansion that produced the tree met on the way — so a state
     * carrying a different one is a different answer, whatever the trees compare as. Left out, the
     * store would find a recomputed answer equal to the one it held and leave everything that reads
     * the standing set on the old one.
     */
    @Override
    public boolean equals(Object o) {
        return o instanceof InvariantSettled other && module.equals(other.module)
                && standing.equals(other.standing);
    }

    @Override
    public int hashCode() {
        return module.hashCode() * 31 + standing.hashCode();
    }

    @Override
    public String toString() {
        return module.toString();
    }
}
