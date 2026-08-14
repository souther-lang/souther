package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.types.TypeKey;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * A declaration in the form every later stage resolves a type against, and the module where every
 * one of them is in it.
 *
 * <p>What is established here is that a newtype construction written {@code 金額(500)} is the
 * construction it is, wherever it is written in what the declaration says about itself. A reader
 * below this compares a construction against what a declaration declares; one that met the
 * application form instead would be reading a call to something no module declares.
 *
 * <p>Two members and they say different things. {@link Def} is one declaration's answer, and a
 * declaration that has no answer costs the readers that name it and no others. {@link Module} is
 * the conjunction — every declaration the module writes has one — which is what a reader wanting the
 * module rather than a declaration is asking for. A module missing a declaration it writes would be
 * read as one that does not declare it, which is a different thing to say and not a true one.
 */
public final class Derived {

    private Derived() {}

    /**
     * One declaration with the newtype constructions in what it says written as constructions.
     *
     * <p>Reached from {@link InvariantSettled.Def} and from nothing else, which is what the measured
     * dependency is: the rewrite reads the clauses of the declaration it is handed, so a declaration
     * whose clauses still name a helper has its constructions left as they were — the helper's body
     * is where they are written, and it is not read.
     *
     * <p>That the settling is worked out for a whole module is a fact about the computation and not
     * about this. What one of these depends on is the settled declaration; where that came from is
     * the query graph's business, and it may go on answering for a module at a time.
     */
    public static final class Def {

        private final Hir.Def def;

        private Def(Hir.Def def) {
            this.def = def;
        }

        /**
         * {@code settled} with its constructions written as constructions.
         *
         * @throws CompileException where what the declaration says cannot be read that way
         */
        public static Def derive(InvariantSettled.Def settled, Symbols scope) {
            return new Def(NewtypeDesugar.rewriteInvariantsOf(settled.def(), scope));
        }

        /** The name it is declared under. */
        public String name() {
            return def.name();
        }

        /** Which declaration it is — the module that wrote it and the name it was written under. */
        public TypeKey declaredKey() {
            return def.declaredKey();
        }

        /**
         * The node.
         *
         * <p>What a registry hands over, and what settles that is the second source it is read
         * beside. {@link Declarations} answers an identity from the compilation's registry and from
         * the language's own vocabulary, and the prelude's declarations are loaded resolved and kept
         * out of derivation — so a vocabulary of these could only be made by claiming of a
         * declaration nothing derived what deriving it would have established. The representation
         * both sources can be in is the node, and this is where the compilation's side reaches it.
         */
        public Hir.Def read() {
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
     * The module where every declaration it writes came out.
     *
     * <p>An assembly and not a stage of its own: each declaration is answered on its own and says
     * what it has to say there, and this is the conjunction of those answers.
     */
    public static final class Module {

        private final Hir.Module module;

        private Module(Hir.Module module) {
            this.module = module;
        }

        /**
         * {@code settled} with each declaration replaced by what that declaration derived to, or
         * null where one of them has no answer.
         *
         * <p>The completeness is the point, so it is asked here rather than remembered: a caller
         * holding one of these is holding a module where every declaration came out, and there is
         * no way to hold one otherwise.
         *
         * <p>Which declaration each answer is for is checked and not taken from the key it arrived
         * under. {@code derived} is keyed by bare name, and a bare name is a name in some module —
         * so an answer for another module's declaration of the same name would otherwise be built
         * into this module, and the claim would be made of a declaration this module does not write.
         *
         * @throws IllegalArgumentException where an answer is for a declaration other than the one
         *     it stands in for
         */
        public static Module assemble(InvariantSettled settled, Map<String, Def> derived) {
            List<Hir.Def> defs = new ArrayList<>();
            for (Hir.Def def : settled.module().defs()) {
                Def came = derived.get(def.name());
                if (came == null) {
                    return null;
                }
                if (!came.declaredKey().equals(def.declaredKey())) {
                    throw new IllegalArgumentException("the declaration derived under `" + def.name()
                            + "` is " + came.declaredKey() + ", not " + def.declaredKey());
                }
                defs.add(came.def);
            }
            Hir.Module m = settled.module();
            return new Module(new Hir.Module(m.name(), m.exposing(), m.exposedOutputs(),
                    m.imports(), defs, m.behaviors(), m.fns(), m.takenOn(), m.examples(), m.fakes(),
                    m.exampleFileTarget(), m.pos()));
        }

        /** What the module is called. */
        public String name() {
            return module.name();
        }

        /** Its definitions, which this state says nothing about — what it declares is what it
         * answered for. */
        public List<Hir.FnDef> fns() {
            return module.fns();
        }

        /** This module's declarations with {@code desugared} standing where its definitions were —
         * what {@link Desugared.Module} is assembled from, which is why it is that state's to ask
         * for rather than anyone's to build. */
        Hir.Module withEachFnDesugared(List<Hir.FnDef> desugared) {
            return new Hir.Module(module.name(), module.exposing(), module.exposedOutputs(),
                    module.imports(), module.defs(), module.behaviors(), desugared,
                    module.takenOn(), module.examples(), module.fakes(), module.exampleFileTarget(),
                    module.pos());
        }

        /**
         * The tree.
         *
         * <p>For a reader asking about the payload rather than about the claim — what shape the
         * module has at this stage, which is a question about the tree and not about what came out.
         * A reader that needs a declaration to have been derived asks for {@link Def}.
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
