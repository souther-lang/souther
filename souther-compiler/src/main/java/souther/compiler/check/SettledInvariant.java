package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.ReachName;

import java.util.SequencedSet;

/**
 * One clause as it was settled, and the calls the expansion that settled it left standing.
 *
 * <p>One value because they are one answer. The tree is what a construction checks and the calls are
 * what the module running that check has to emit a method for, and both came out of the one
 * expansion. Read from two places, a reader could type a tree whose calls nothing emits, or emit for
 * calls no tree makes. A clause carried to another module is the case it matters for: the tree
 * travels with the declaration, and the calls have to travel with it rather than stay with the
 * module that expanded it.
 *
 * <p>Which declaration wrote it is not here. Whoever holds one asked a declaration for it, and a
 * second statement of which one would be something the two could disagree about.
 */
public final class SettledInvariant {

    private final Hir.InvariantClause clause;
    private final CallsLeftStanding standing;

    SettledInvariant(Hir.InvariantClause clause, CallsLeftStanding standing) {
        if (clause == null || standing == null) {
            throw new IllegalArgumentException(
                    "a settled clause is a tree and what its expansion left standing");
        }
        this.clause = clause;
        this.standing = standing;
    }

    /** The clause. */
    public Hir.InvariantClause clause() {
        return clause;
    }

    /** The calls its expansion left standing, in the order the expansion met them — each one a
     *  helper the module that runs the clause emits as a method. */
    public SequencedSet<ReachName.Declaration> callsLeftStanding() {
        return standing.calls();
    }

    /**
     * The same clause as {@code reader} reaches what it names.
     *
     * <p>The tree and the calls together, so what the tree applies and what the calls name are the
     * same routes after this as before it.
     */
    public SettledInvariant reachedFrom(String reader) {
        return new SettledInvariant(clause.with(HelperNames.reachedFrom(clause.expr(), reader)),
                standing.reachedFrom(reader));
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof SettledInvariant other && clause.equals(other.clause)
                && standing.equals(other.standing);
    }

    @Override
    public int hashCode() {
        return clause.hashCode() * 31 + standing.hashCode();
    }

    @Override
    public String toString() {
        return clause + " leaving " + standing;
    }
}
