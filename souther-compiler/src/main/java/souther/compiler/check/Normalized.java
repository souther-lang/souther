package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.types.TypeKey;

/**
 * A declaration in the form every reader below the settling reads one: the newtype constructions in
 * what it says about itself, written as the constructions they denote.
 *
 * <p>Its own rung, between the settling and the derivation, because it is its own achievement.
 * Normalizing a declaration is declaration-local — the clauses are rewritten against what names
 * mean, and nothing else is asked — so it is answered for every declaration a module writes.
 * Deriving a boundary representation is not: it reads the declared shape, and a product one of
 * whose fields names no type has none to read. Two achievements with two preconditions.
 *
 * <p>Held apart because of what happened when they were one. The normalized declaration was
 * reachable only through the table of derived ones, so which form a reader was handed — the
 * constructions written as constructions, or the calls the author typed — turned on whether a codec
 * could be derived. That is a question the reader did not ask and could not see the answer to, and
 * two declarations of one module came back in two forms.
 */
public final class Normalized {

    private Normalized() {}

    /**
     * One declaration, normalized.
     *
     * <p>Which kind it is, is what the three cases say, so a reader that has to tell them apart
     * switches over them rather than over the node inside.
     */
    public sealed interface Def permits Data, Sum, Unit {

        /**
         * {@code settled} with the constructions in its clauses written as constructions.
         *
         * <p>Answered for every declaration, and that is what makes this a rung a reader can be
         * answered from. A newtype applied to something other than one value is not a construction
         * of it and is left the application it is; what is wrong with it is said by the reading that
         * refuses it ({@link NewtypeDesugar#refuseMalformedIn}) rather than by this coming back with
         * nothing. Refusing here, this would be a producer whose failure decides what a declaration
         * means to every reader below — which is the shape it is written to stop.
         */
        static Def of(InvariantSettled.Def settled, ResolvedSymbols scope) {
            return over(NewtypeDesugar.rewriteInvariantsOf(settled.def(), scope));
        }

        /**
         * What {@link #of} could not write as a construction, of the same declaration.
         *
         * <p>Beside the answer and not instead of it. The two read one question off one node — a
         * name this module resolved to a newtype, applied — and they part on the count: applied to
         * one value it is a construction and is written as one, applied to anything else it is not
         * one and is wrong where it was written.
         *
         * @throws CompileException at the first such application, where there is one
         */
        static void refuseMalformedIn(InvariantSettled.Def settled, ResolvedSymbols scope) {
            NewtypeDesugar.refuseMalformedIn(settled.def(), scope);
        }

        /**
         * What the language itself declares.
         *
         * <p>Every kind of it, and a product among them, because normalizing is something a
         * declaration of any kind has had done to it once its clauses hold no unwritten
         * construction — and what the library declares holds none. A product is refused one rung
         * up ({@link Derived.Def#ofLanguage}) and refused there for the other reason: it would need
         * a representation derived.
         */
        static Def ofLanguage(Hir.Def declared) {
            return over(declared);
        }

        private static Def over(Hir.Def node) {
            return switch (node) {
                case Hir.Data d -> new Data(d);
                case Hir.SumData s -> new Sum(s);
                case Hir.UnitData u -> new Unit(u);
            };
        }

        /** The declaration node, in this form. */
        Hir.Def node();

        /** The name it is declared under. */
        default String name() {
            return node().name();
        }

        /** Which declaration it is — the module that wrote it and the name it was written under. */
        default TypeKey declaredKey() {
            return node().declaredKey();
        }
    }

    /** A product, normalized. */
    public static final class Data implements Def {

        private final Hir.Data node;

        private Data(Hir.Data node) {
            this.node = node;
        }

        @Override
        public Hir.Data node() {
            return node;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Data other && node.equals(other.node);
        }

        @Override
        public int hashCode() {
            return node.hashCode();
        }
    }

    /** A sum, normalized. */
    public static final class Sum implements Def {

        private final Hir.SumData node;

        private Sum(Hir.SumData node) {
            this.node = node;
        }

        @Override
        public Hir.SumData node() {
            return node;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Sum other && node.equals(other.node);
        }

        @Override
        public int hashCode() {
            return node.hashCode();
        }
    }

    /** A unit, normalized. */
    public static final class Unit implements Def {

        private final Hir.UnitData node;

        private Unit(Hir.UnitData node) {
            this.node = node;
        }

        @Override
        public Hir.UnitData node() {
            return node;
        }

        @Override
        public boolean equals(Object o) {
            return o instanceof Unit other && node.equals(other.node);
        }

        @Override
        public int hashCode() {
            return node.hashCode();
        }
    }
}
