package souther.compiler.check;

import souther.compiler.ast.Ast;

/**
 * A module {@code Resolve} has read: one holding no occurrence anything is still to answer.
 *
 * <p>Not a module whose names all answer to something. Resolution finishing and every name finding
 * a declaration are two things, which is what {@link Ast.Name.Unanswered} and
 * {@link Ast.Var.Unanswered} are for — a name nothing declares was read, was reported where it is
 * written, and is as answered as the pass can make it. What this says is the other one: the pass has
 * been over this tree, so nothing in it is {@link Ast.Name.Written}, {@link Ast.Var.Written} or
 * {@link Ast.TypeRef.Written}.
 *
 * <p>The three node types say it for themselves at each occurrence; this says it of the whole, which
 * is what a signature can carry. {@code Resolve} states the invariant in prose and every consumer
 * kept it by looking (issues #464, #696, #700); a consumer that is handed one of these cannot ask
 * for a resolution, because it holds nothing to resolve.
 *
 * <p>It does not make the unread state unrepresentable at each occurrence. A switch over
 * {@link Ast.Var} is total over three records whatever module the value came out of, so a reader
 * still writes an arm for the one that cannot be there and refuses it. What this removes is the
 * question being asked again at every consumer, not the arm.
 *
 * <p>Minted in this package and nowhere else — the constructor is package-private, and
 * {@link Resolve} is what calls it. A pass that rewrites a resolved tree goes through
 * {@link #with(Ast.Module)}, which is the same claim made again by whoever is making it: the pass
 * mints its nodes resolved, as {@code Deriver}, {@code NewtypeDesugar}, {@code HelperInliner} and
 * {@code FixtureTemplate} already do.
 */
public final class ResolvedModule {

    private final Ast.Module module;

    ResolvedModule(Ast.Module module) {
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
    public Ast.Module module() {
        return module;
    }

    /**
     * {@code rewritten} as a resolved module, for a pass that rewrote this one.
     *
     * <p>Asked of the module it came from, so the claim is made where a resolved tree already is
     * rather than anywhere a tree can be built. What a pass writes into one it mints resolved, which
     * is what every pass after {@code Resolve} already does.
     */
    public ResolvedModule with(Ast.Module rewritten) {
        return new ResolvedModule(rewritten);
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof ResolvedModule other && module.equals(other.module);
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
