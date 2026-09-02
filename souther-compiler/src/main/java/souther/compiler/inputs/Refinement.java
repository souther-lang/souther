package souther.compiler.inputs;

import souther.compiler.types.ResolvedCase;
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
 *
 * <p><b>Made only from a value that already settles which narrowing it is.</b> Two vocabularies
 * decide that — what a position's type divides into ({@link Case}) and what a written pattern was
 * resolved to select ({@link ResolvedCase}) — and each has a way in here. What has no way in is a
 * name, and a name falls short twice over. An optional's present carrier and a sum's case are both
 * called {@code Some} where one is written, so a narrowing built from the name is one of the two
 * chosen by whoever built it. And a case that is itself a sum is one name over several leaves,
 * while a position divides into the leaves, so a narrowing built from that name is a place the
 * reading has none of. Every reader below compares narrowings by equality, so a path spelled either
 * way never meets the position it was meant to be about.
 */
public sealed interface Refinement {

    /** How a path writes it, which is what a report names the position by. */
    String spelled();

    /**
     * The same, with which kind of narrowing it is said as well.
     *
     * <p>For a message about this compiler and never for a report about a model. Two narrowings of
     * unlike kinds can be written the same way — {@code @Some} is an optional's present carrier
     * where an optional stands and a sum's case where one is declared with that name — so a
     * diagnostic that spelled only the path would say two unequal positions are one, which is what
     * an author is told when the compiler is the one that is confused.
     */
    String discriminated();

    /**
     * The narrowing {@code one} is, or null where sitting in that distinction narrows no position.
     *
     * <p>The one way in for a reader that has what a position's type divides into. What a position
     * divides into and what a position under it stands beneath are the same statement read twice —
     * a row whose value is an {@code Approved} is a row at every position {@code Approved} declares
     * — and a second relating of them would be the classes and the branches disagreeing about which
     * is which. {@link #of(CaseSelector)} is beside this and is not that second relating: it takes
     * what a checked pattern selected, which is the other value that settles a narrowing, and the
     * two are held to one answer where a type states a division a pattern can select.
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
            case Case.SumCase sum -> new SumCase(sum.leaf());
            case Case.Presence presence -> new Presence(presence.present());
            case Case.Truth _, Case.Named _ -> null;
        };
    }

    /**
     * The narrowing {@code selected} is, or null where selecting it narrows a position to no one
     * distinction.
     *
     * <p>The same relating of vocabularies as {@link #of(Case)} and from the other end. A position's
     * type says what it divides into; a checked pattern says which of those divisions the arm took.
     * Both settle a narrowing on their own, and a reader that has one of them has no second question
     * to ask.
     *
     * <p><b>Read off what the selection was resolved to, and never off the name it was written
     * by.</b> Two facts settle it and neither is the name. What the value turns out to be tells an
     * optional's present carrier from a sum's case declared under the same word — a reader taking
     * the name would build the sum's narrowing for both. And which leaves the selection covers tells
     * a case that divides the position from one that is itself divided: a case that is a sum stands
     * for the leaves under it (spec §sum-data), and the reading of a position divides it into those
     * leaves ({@link Distinctions}), so an arm naming the case above them narrows to several of them
     * and to no one of them. Read from the name, {@code @OnceKind} would be written where the
     * reading holds {@code @Station} and {@code @Hospital}.
     *
     * <p>So a narrowing is the leaf itself and not the name it was reached by. A case declared over
     * one leaf is written as that leaf here, which is how the position spells it.
     *
     * <p>Null and not a refusal. An arm can select a case that divides nothing at a position, the
     * way a {@code Bool}'s two values divide none, and what a reader is owed for one is that there
     * is no narrowing here — the same answer {@link #of(Case)} gives for the distinctions that put
     * nothing under them.
     *
     * <p>Exhaustive over {@link souther.compiler.types.Refinement}, with no {@code default}: a way
     * of selecting a case added later stops this compiling rather than arriving as whichever arm is
     * nearest.
     */
    static Refinement of(ResolvedCase selected) {
        return switch (selected.refinement()) {
            case souther.compiler.types.Refinement.Direct _ -> selected.atoms().size() == 1
                    ? new SumCase(selected.atoms().get(0)) : null;
            // An optional's carriers cover themselves and are not leaves of anything, so what they
            // narrow to follows from the carrier alone ({@code CaseSpace}).
            case souther.compiler.types.Refinement.OptionPresent _ -> new Presence(true);
            case souther.compiler.types.Refinement.OptionAbsent _ -> new Presence(false);
        };
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
        public String discriminated() {
            return spelled() + "[sum-case]";
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
        public String discriminated() {
            return spelled() + "[presence]";
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
