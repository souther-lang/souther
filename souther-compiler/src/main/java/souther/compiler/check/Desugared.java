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
         */
        public static Module assemble(Derived.Module derived, Map<String, Fn> desugared) {
            List<Hir.FnDef> fns = new ArrayList<>();
            for (Hir.FnDef fn : derived.fns()) {
                Fn came = desugared.get(fn.name());
                if (came == null) {
                    return null;
                }
                fns.add(came.fn);
            }
            return new Module(derived.withEachFnDesugared(fns));
        }

        /** What the module is called. */
        public String name() {
            return module.name();
        }

        /**
         * The same module with every imported name written as the definition it denotes.
         *
         * <p>A transformation and not a projection: what comes back is desugared too — writing a
         * name qualified does not touch a construction — and it is handed over as a tree all the
         * same, so the claim stops here. It is the one reader's, and that reader is the state above
         * this one: whatever holds "imports qualified" is where this belongs, and it should take
         * this state rather than a tree when it exists.
         */
        public Hir.Module withImportsQualified() {
            return HelperNames.qualifyImports(module);
        }

        /**
         * The tree.
         *
         * <p>Wider than its one reader needs. What asks for it is the behavior signatures, which
         * read what the module declared and nothing this state says; the projection it wants is
         * those behaviors, and this hands over everything. It goes when that reader is migrated,
         * rather than being the way a reader gets at the payload.
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
