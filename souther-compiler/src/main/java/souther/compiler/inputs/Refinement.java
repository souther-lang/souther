package souther.compiler.inputs;

import souther.compiler.types.TypeSymbol;

/**
 * A narrowing of which values may stand at a position, which does not move to another position.
 *
 * <p>The distinction between this and a step of a path is the whole of what it is for. A field and
 * an element go somewhere: the value at the end of one is inside the value at the start of it. A
 * refinement goes nowhere — {@code d@Approved} is the same value {@code d} is, read as the case it
 * turned out to be — and what it buys is that the positions the case declares can be named at all.
 *
 * <p>Not one kind of narrowing. A sum states its cases and an optional states whether it holds
 * anything, and {@link Case} already reads both as distinctions of one kind; a refinement written
 * for cases alone would be a second reading of that, and the optional would arrive later as a
 * shape of its own with nothing to be an instance of.
 */
public sealed interface Refinement {

    /** How a path writes it, which is what a report names the position by. */
    String spelled();

    /**
     * The narrowing {@code one} is, or null where sitting in that distinction narrows no position.
     *
     * <p>The one place the two vocabularies are related. What a position divides into and what a
     * position under it stands beneath are the same statement read twice — a row whose value is an
     * {@code Approved} is a row at every position {@code Approved} declares — and a second relating
     * of them would be the classes and the branches disagreeing about which is which.
     *
     * <p>Exhaustive over {@link Case}, with no {@code default}: a distinction the reading learns to
     * make later stops this compiling rather than arriving as a branch that is quietly never walked.
     *
     * <p>Null for the two that divide a position without putting anything under it. A {@code Bool}
     * is two values and holds no position; a value a rule singled out is one value of the position
     * and is not a case of it.
     */
    static Refinement of(Case one) {
        return switch (one) {
            case Case.SumCase sum -> sumCase(sum.leaf());
            case Case.Presence presence -> new Presence(presence.present());
            case Case.Truth _, Case.Named _ -> null;
        };
    }

    /**
     * The narrowing to {@code leaf}, for a caller that already has the case and not the distinction.
     *
     * <p>Not a second correspondence. {@link #of} relates two vocabularies — what a position divides
     * into, and what a position under it stands beneath — and a caller holding a {@code match} arm's
     * case has not asked that question: which case the arm selected was settled where the arm was
     * read. Sent back through {@link Distinctions} to be turned into a {@link Case} first, it would
     * be a reader re-deriving what it was already told, which is the arrangement this vocabulary
     * exists to stop.
     *
     * <p>Here rather than at a constructor, so that what a narrowing is stays this type's to say.
     */
    static Refinement sumCase(TypeSymbol leaf) {
        return new SumCase(leaf);
    }

    /**
     * The value turned out to be this case of the sum standing at the position.
     *
     * <p>A class and not a record so that the canonical way in can be closed: nothing outside this
     * declaration may spell a narrowing, because a narrowing spelled somewhere else is a second
     * reading of which distinctions narrow a position. Compared by what it narrows to all the same —
     * every reader that decides whether two requirements hold together does it by equality
     * ({@link Requirements#merge}), and an identity comparison here would have no two narrowings
     * ever agree.
     */
    final class SumCase implements Refinement {

        /** The case, folded to a leaf as {@link Distinctions} folds the cases it reads. */
        private final TypeSymbol leaf;

        private SumCase(TypeSymbol leaf) {
            if (leaf == null) {
                throw new IllegalArgumentException("a narrowing to no case is not one");
            }
            this.leaf = leaf;
        }

        public TypeSymbol leaf() {
            return leaf;
        }

        @Override
        public String spelled() {
            return leaf.name();
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof SumCase that && leaf.equals(that.leaf);
        }

        @Override
        public int hashCode() {
            return leaf.hashCode();
        }

        @Override
        public String toString() {
            return "SumCase[leaf=" + leaf + "]";
        }
    }

    /**
     * The optional standing at the position holds a value, or holds none.
     *
     * <p>{@code Some} refines the position to what the optional holds, and does not descend to it:
     * what an optional holds is at no name of its own, exactly as what a newtype wraps is
     * ({@link TermPath}). So the position under it is {@code x@Some} and never {@code x@Some.value}
     * — the second would be a location this compiler invented, spelled by nothing else that reads
     * the same value.
     *
     * <p>A class for the reason {@link SumCase} is, and compared the same way.
     */
    final class Presence implements Refinement {

        private final boolean present;

        private Presence(boolean present) {
            this.present = present;
        }

        public boolean present() {
            return present;
        }

        @Override
        public String spelled() {
            return present ? "Some" : "None";
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Presence that && present == that.present;
        }

        @Override
        public int hashCode() {
            return Boolean.hashCode(present);
        }

        @Override
        public String toString() {
            return "Presence[present=" + present + "]";
        }
    }
}
