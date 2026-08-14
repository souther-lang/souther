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
         * @throws CompileException where a construction written in the body cannot be read as one
         */
        public static Fn desugar(Hir.FnDef fn, Symbols scope) {
            return new Fn(NewtypeDesugar.rewriteOf(fn, scope));
        }

        /** What the definition is called. */
        public String name() {
            return fn.name();
        }

        /** The node, for the module this one is assembled into. Nothing outside asks for a
         * definition on its own: what reads one is below the module the assembly answers with. */
        Hir.FnDef fn() {
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

        private final Hir.Module module;

        private Module(Hir.Module module) {
            this.module = module;
        }

        /**
         * {@code derived} with each definition replaced by what that definition desugared to, or
         * null where one of them has no answer.
         *
         * <p>What it declares is what {@link Derived.Module} answered for, so both conjunctions are
         * in this one value: every declaration came out, and every definition did.
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
            List<Hir.FnDef> fns = new ArrayList<>();
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
                fns.add(came.fn);
            }
            return new Module(derived.withEachFnDesugared(fns));
        }

        /** What the module is called. */
        public String name() {
            return module.name();
        }

        /** The tree, for the state above this one, which is what qualifies its imports. */
        Hir.Module module() {
            return module;
        }

        /**
         * The behaviors this module declares.
         *
         * <p>What the signatures are made from, and the whole of what that reader wanted. It read
         * the module before, which handed it everything this state says about the definitions as
         * well — a claim it does not use and could drop without anything saying so.
         */
        public List<Hir.BehaviorDef> behaviors() {
            return module.behaviors();
        }

        /**
         * The tree at this stage.
         *
         * <p>No reader in the compiler asks for this. What is left is the two tests that audit the
         * payload at each stage — whether every tree a compile makes is still well founded, and
         * whether what a module declares changes as the stages rewrite it — and neither leans on
         * what this state claims; they ask about the tree, which is what they are for.
         */
        public Hir.Module tree() {
            return module;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Module other && module.equals(other.module);
        }

        @Override
        public int hashCode() {
            return module.hashCode();
        }
    }
}
