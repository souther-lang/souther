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
     *
     * <p>Which kind of declaration it is, is what the three cases say, and a reader that has to tell
     * them apart switches over them rather than over the node inside. The kinds are the ones a
     * declaration can be, so what a later stage adds to one of them has somewhere to go that the
     * others do not reach.
     */
    public sealed interface Def permits Data, Sum, Unit {

        /**
         * {@code settled} with its constructions written as constructions.
         *
         * @throws CompileException where what the declaration says cannot be read that way
         */
        static Def derive(InvariantSettled.Def settled, Symbols scope) {
            return switch (NewtypeDesugar.rewriteInvariantsOf(settled.def(), scope)) {
                case Hir.Data d -> new Data(d);
                case Hir.SumData s -> new Sum(s);
                case Hir.UnitData u -> new Unit(u);
            };
        }

        /**
         * The declaration this was derived from, as resolution left it.
         *
         * <p>One declaration at a time and never a table. What is read through this is what a
         * declaration says about itself whatever stage is reading — its fields, what it includes,
         * whether it is a newtype — and a reader wanting any of that is asking about the resolution
         * and not about this stage. A table of these, turned back into a table of nodes, is the
         * other thing entirely: it hands every reader below the stage a declaration with nothing
         * left saying it reached it.
         */
        Hir.Def declared();

        /** The name it is declared under. */
        default String name() {
            return declared().name();
        }

        /** Which declaration it is — the module that wrote it and the name it was written under. */
        default TypeKey declaredKey() {
            return declared().declaredKey();
        }
    }

    /** A product declaration that came out. */
    public static final class Data implements Def {

        private final Hir.Data declared;

        private Data(Hir.Data declared) {
            this.declared = declared;
        }

        @Override
        public Hir.Data declared() {
            return declared;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Data other && declared.equals(other.declared);
        }

        @Override
        public int hashCode() {
            return declared.hashCode();
        }
    }

    /** A sum declaration that came out. */
    public static final class Sum implements Def {

        private final Hir.SumData declared;

        private Sum(Hir.SumData declared) {
            this.declared = declared;
        }

        @Override
        public Hir.SumData declared() {
            return declared;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Sum other && declared.equals(other.declared);
        }

        @Override
        public int hashCode() {
            return declared.hashCode();
        }
    }

    /** A unit declaration that came out. */
    public static final class Unit implements Def {

        private final Hir.UnitData declared;

        private Unit(Hir.UnitData declared) {
            this.declared = declared;
        }

        @Override
        public Hir.UnitData declared() {
            return declared;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Unit other && declared.equals(other.declared);
        }

        @Override
        public int hashCode() {
            return declared.hashCode();
        }
    }

    /**
     * The module where every declaration it writes came out.
     *
     * <p>An assembly and not a stage of its own: each declaration is answered on its own and says
     * what it has to say there, and this is the conjunction of those answers.
     */
    public static final class Module {

        private final InvariantSettled settled;
        private final List<Def> defs;
        /** Worked out once. The parts are what this holds; the tree is the shape they take, and a
         *  rung above asks for it every time it rewrites one of its own parts. */
        private volatile Hir.Module projected;

        private Module(InvariantSettled settled, List<Def> defs) {
            this.settled = settled;
            this.defs = List.copyOf(defs);
        }

        /**
         * {@code settled} with each declaration replaced by what that declaration derived to, or
         * null where one of them has no answer.
         *
         * <p>The completeness is the point, so it is asked here rather than remembered: a caller
         * holding one of these is holding a module where every declaration came out, and there is
         * no way to hold one otherwise.
         *
         * <p>What comes out holds the answers. Pouring them into a tree would leave the module
         * saying every declaration came out and no declaration of it saying so, which is where the
         * rungs above lost the claim (#714): a state built from a tree has nothing but nodes to
         * answer a route with.
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
            List<Def> defs = new ArrayList<>();
            for (Hir.Def def : settled.module().defs()) {
                Def came = derived.get(def.name());
                if (came == null) {
                    return null;
                }
                if (!came.declaredKey().equals(def.declaredKey())) {
                    throw new IllegalArgumentException("the declaration derived under `" + def.name()
                            + "` is " + came.declaredKey() + ", not " + def.declaredKey());
                }
                defs.add(came);
            }
            return new Module(settled, defs);
        }

        /** What the module is called. */
        public String name() {
            return settled.name();
        }

        /** Its declarations, each of them the derived declaration and not the node. */
        public List<Def> defs() {
            return defs;
        }

        /** The behaviors this module declares, which no rung at or below this one rewrites. */
        public List<Hir.BehaviorDef> behaviors() {
            return settled.module().behaviors();
        }

        /** Its definitions, which this state says nothing about — what it declares is what it
         * answered for. */
        public List<Hir.FnDef> fns() {
            return settled.fns();
        }

        /**
         * The parts written back into the shape a pass over a whole module takes.
         *
         * <p>One direction only. What this module declares is the list above; this is that list
         * projected, and nothing reads a module back into parts — a state made that way would be
         * claiming of nodes what was established of the answers they replaced.
         */
        Hir.Module module() {
            Hir.Module built = projected;
            if (built == null) {
                List<Hir.Def> nodes = new ArrayList<>();
                for (Def def : defs) {
                    nodes.add(def.declared());
                }
                projected = built = settled.module().withDefs(nodes);
            }
            return built;
        }

        /**
         * The same, for the tests that audit what a module carries at each stage.
         *
         * <p>They ask about the payload rather than about the claim — what shape the module has
         * here — which is what this is for and the whole of it. A reader in the compiler that needs
         * a declaration to have been derived asks for {@link Def}.
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
