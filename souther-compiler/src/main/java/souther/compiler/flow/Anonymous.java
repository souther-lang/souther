package souther.compiler.flow;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;

/**
 * The naming with no words for anything.
 *
 * <p>What a reader asking only whether an expression arrives at a value uses. Every path is the same
 * path, so the arrivals of a node collapse to what they come to and no further — at most one per
 * {@link Truth}, which is what keeps this reading linear in the size of the body.
 *
 * <p>Nothing here is {@link Completeness#PARTIAL}. A naming that has no words for conditions has none
 * missing either: what it writes down is all it set out to write down, and a reader that wanted the
 * conditions would not be using this one.
 */
public final class Anonymous implements Naming<AnonymousPath> {

    public static final Anonymous NAMING = new Anonymous();

    private Anonymous() {}

    @Override
    public AnonymousPath nowhere() {
        return AnonymousPath.INSTANCE;
    }

    @Override
    public AnonymousPath join(AnonymousPath held, AnonymousPath more) {
        return AnonymousPath.INSTANCE;
    }

    @Override
    public Naming<AnonymousPath> under(Hir.Binder binder, Core value) {
        return this;
    }

    @Override
    public AnonymousPath side(Core.Binary comparison, boolean held) {
        return AnonymousPath.INSTANCE;
    }

    @Override
    public AnonymousPath matchCase(Core.Match match, int part) {
        return AnonymousPath.INSTANCE;
    }

    @Override
    public AnonymousPath forkArm(Core fork, int part) {
        return AnonymousPath.INSTANCE;
    }

    @Override
    public int mostArrivals() {
        // Three truths and one path, so nothing here can go over it. Written down all the same: a
        // reader takes the bound from the naming and does not ask which naming it has.
        return 3;
    }
}
