package souther.compiler.check;

import souther.compiler.ast.Hir;

/**
 * A module {@code Resolve} has read: one holding no occurrence anything is still to answer.
 *
 * <p>Not a module whose names all answer to something. Resolution finishing and every name finding
 * a declaration are two things, which is what {@link Hir.Name.Unanswered} and
 * {@link Hir.Var.Unanswered} are for — a name nothing declares was read, was reported where it is
 * written, and is as answered as the pass can make it. What this says is the other one: the pass has
 * been over this tree — which is what its being a {@link Hir} says, since no reference occurrence of
 * that representation has a form for one nothing has read.
 *
 * <p>The three node types say it for themselves at each occurrence; this says it of the whole, which
 * is what a signature can carry. {@code Resolve} states the invariant in prose and every consumer
 * kept it by looking (issues #464, #696, #700); a consumer that is handed one of these cannot ask
 * for a resolution, because it holds nothing to resolve.
 *
 * <p>It does not make the unread state unrepresentable at each occurrence. A switch over
 * {@link Hir.Var} is total over three records whatever module the value came out of, so a reader
 * still writes an arm for the one that cannot be there and refuses it. What this removes is the
 * question being asked again at every consumer, not the arm.
 *
 * <p>The first rung, and the only one that hands its tree over. What it claims is what {@link Hir}
 * itself claims, so a reader holding the tree holds the claim; the rungs above say something the
 * payload does not carry, and those keep their trees. There is no operation here that takes a tree
 * and answers a resolved module: a pass that rewrites one either states what it has established
 * — {@link Expandable}, {@link InvariantSettled} — or answers a tree, which claims nothing.
 */
public final class Resolved {

    private final Hir.Module module;

    /** Minted in this package and nowhere else — {@link Resolve} is what calls it. */
    Resolved(Hir.Module module) {
        if (module == null) {
            throw new IllegalArgumentException("a resolved module is a module");
        }
        this.module = module;
    }

    /** What the module is called. */
    public String name() {
        return module.name();
    }

    /** The tree. */
    public Hir.Module module() {
        return module;
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof Resolved other && module.equals(other.module);
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
