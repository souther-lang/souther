package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * A definition whose newtype constructions are written as constructions, and the module where every
 * definition of it is one.
 *
 * <p>{@code 金額(500)} is written like a call and is not one — no module declares a {@code 金額} a
 * value position could apply. A reader that met the application form would be reading a call to
 * something nothing declares, which is what {@code CallElaborator} says of it where it says the
 * form cannot reach there.
 *
 * <p>What this does <em>not</em> claim is anything about the parameter types the definition carries.
 * A helper parameter the author left unwritten is settled before this, and that settling is
 * best-effort by contract: one its body does not determine is left as it was, for the check below to
 * report. So the annotations are in the tree here and there is no proposition about them to hold —
 * a state named for them would be naming a pass that ran rather than a fact a reader may lean on.
 */
public final class Desugared {

    private Desugared() {}

    /** One definition with the newtype constructions in its body written as constructions. */
    public static final class Fn {

        private final Hir.FnDef fn;

        private Fn(Hir.FnDef fn) {
            this.fn = fn;
        }

        /**
         * {@code fn} with its constructions written as constructions.
         *
         * <p>Of the definition it is handed. What a newtype is comes from the symbols rather than
         * from anything the definition has been through, so this asks nothing of where it came from
         * — measured, by rewriting a definition of a settled module and of an unsettled one and
         * getting the same answer.
         *
         * <p>Answered for every definition. A rewrite is not a check: what it writes as a
         * construction is a newtype applied to one value, and an application of one to any other
         * count is left as the application it is, to be said where the check reads it
         * ({@code CallElaborator.noCallee}). A refusal here would make a body nobody could read into
         * a definition nobody could see, and a module is assembled from all of them.
         */
        public static Fn desugar(Hir.FnDef fn, Symbols scope) {
            return new Fn(NewtypeDesugar.rewriteOf(fn, scope));
        }


        /**
         * This state, of a definition a rung above rewrote after it was desugared.
         *
         * <p>Not the rewrite run again for its effect. What is asked is whether the proposition
         * still holds of the node that came out, and the answer is this state or a refusal — a rung
         * that carried the old value's state across its own rewrite would be saying of the new node
         * what was established of the old one.
         *
         * <p>So the rewrite is run and its result is compared, rather than taken. Today the two are
         * the same for every definition a compile prepares, and if the desugaring ever came to do
         * more than decide a form — mint a name, move a position — the difference would be a
         * re-transformation wearing a re-proof's name, and this is where it stops.
         *
         * @throws IllegalArgumentException where the definition is not one this state holds of
         * @throws CompileException where a construction written in the body cannot be read as one
         */
        public static Fn reestablish(Hir.FnDef rewritten, Symbols scope) {
            Hir.FnDef again = NewtypeDesugar.rewriteOf(rewritten, scope);
            if (!again.equals(rewritten)) {
                throw new IllegalArgumentException("`" + rewritten.name()
                        + "` is not a definition whose constructions are constructions");
            }
            return new Fn(rewritten);
        }

        /** What the definition is called. */
        public String name() {
            return fn.name();
        }

        /**
         * The node.
         *
         * <p>For a reader that holds this state and walks what is in it. Handing it over does not
         * let the claim go: a reader arrives here having been given one of these, which is what its
         * own signature had to ask for, and there is no way to make one out of a definition nothing
         * desugared.
         */
        public Hir.FnDef read() {
            return fn;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Fn other && fn.equals(other.fn);
        }

        @Override
        public int hashCode() {
            return fn.hashCode();
        }
    }

    /** The module where every definition it writes came out, over the declarations that came out. */
    public static final class Module {

        private final Derived.Module derived;
        private final List<Fn> fns;
        /** Worked out once, as {@link Derived.Module#module()} is. */
        private volatile Hir.Module projected;

        private Module(Derived.Module derived, List<Fn> fns) {
            this.derived = derived;
            this.fns = List.copyOf(fns);
        }

        /**
         * {@code derived} with each definition replaced by what that definition desugared to, or
         * null where one of them has no answer.
         *
         * <p>What it declares is what {@link Derived.Module} answered for, so both conjunctions are
         * in this one value: every declaration came out, and every definition did. It holds the
         * state below rather than that state's tree, which is what keeps the first of them
         * reachable from here — a module assembled out of nodes can answer a route with nothing else
         * (#714).
         *
         * <p>Which definition each answer is for is checked and not taken from the key it arrived
         * under, for the reason {@link Derived.Module#assemble} states of declarations: a module
         * carries definitions of several modules under names of one shape, and which module wrote
         * each is on the definition.
         *
         * @throws IllegalArgumentException where an answer is for a definition other than the one it
         *     stands in for
         */
        public static Module assemble(Derived.Module derived, Map<String, Fn> desugared) {
            List<Fn> fns = new ArrayList<>();
            for (Hir.FnDef fn : derived.fns()) {
                Fn came = desugared.get(fn.name());
                if (came == null) {
                    return null;
                }
                if (!came.fn.name().equals(fn.name())
                        || !java.util.Objects.equals(came.fn.declaredIn(), fn.declaredIn())) {
                    throw new IllegalArgumentException("the definition desugared under `" + fn.name()
                            + "` is `" + came.fn.name() + "` of " + came.fn.declaredIn()
                            + ", not `" + fn.name() + "` of " + fn.declaredIn());
                }
                fns.add(came);
            }
            return new Module(derived, fns);
        }

        /** What the module is called. */
        public String name() {
            return derived.name();
        }

        /** Whether this was built over {@code settling}, asked of the rung below for the reason
         *  {@link Derived.Module#settledFrom} gives. */
        boolean settledFrom(InvariantSettled settling) {
            return derived.settledFrom(settling);
        }

        /** Its declarations, which the rung below answered for and this one does not touch. */
        public List<Derived.Def> defs() {
            return derived.defs();
        }

        /** Its definitions, each of them the desugared definition and not the node. */
        public List<Fn> fns() {
            return fns;
        }

        /**
         * The behaviors this module declares.
         *
         * <p>What the signatures are made from, and the whole of what that reader wanted. Nothing
         * at or below this rung rewrites a behavior — measured over a compile of the suite, where
         * what a module prepares carries the behaviors resolution left, every time.
         */
        public List<Hir.BehaviorDef> behaviors() {
            return derived.behaviors();
        }

        /** The parts written back into the shape a pass over a whole module takes, as
         *  {@link Derived.Module#module()} is, and in the same one direction. */
        Hir.Module module() {
            Hir.Module built = projected;
            if (built == null) {
                List<Hir.FnDef> nodes = new ArrayList<>();
                for (Fn fn : fns) {
                    nodes.add(fn.read());
                }
                projected = built = derived.module().withFns(nodes);
            }
            return built;
        }

        /**
         * The same, for the tests that audit the payload at each stage — whether every tree a
         * compile makes is still well founded, and whether what a module declares changes as the
         * stages rewrite it. Neither leans on what this state claims; they ask about the tree,
         * which is what this is for.
         */
        public Hir.Module tree() {
            return module();
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Module other && module().equals(other.module());
        }

        @Override
        public int hashCode() {
            return module().hashCode();
        }
    }
}
