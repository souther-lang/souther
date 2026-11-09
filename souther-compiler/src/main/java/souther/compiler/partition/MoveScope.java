package souther.compiler.partition;

import java.util.Set;

/**
 * Which positions a search that asks what a body answers may move, and which it leaves where the
 * origin stands.
 *
 * <p>A position is left standing only where moving it can change nothing the search asks. That
 * takes two things to hold together, and a position either has both or is moved:
 *
 * <ul>
 *   <li>What the rules require of a position is on its own parameter. A rule names the paths under
 *       the value it belongs to ({@code RuleRoots}), so another parameter's value is no
 *       condition of whether this one is valid, and the origin's value stands as a value of its
 *       parameter wherever the others are moved.
 *   <li>What the body answers does not turn on it. A parameter the body never reads has every
 *       value answer alike, so a row that tells a rewrite apart, or goes through an arm, does so
 *       at the origin's value of it as at any other.
 * </ul>
 *
 * <p>Held per parameter and never per position: a parameter read anywhere is moved everywhere,
 * since which of its positions the body decides on is the reading's question and not this one's.
 * Where nothing is known of what the body reads, every position is moved.
 *
 * <p>So a row found with the unread parameters moved is a row found with them standing, and one
 * that is not found with them standing is not found by moving them. What this changes is only how
 * much of a budget is spent on moves that cannot tell: the order of the names, and how many
 * parameters the body ignores, no longer decide which candidates the budget reaches.
 */
final class MoveScope {

    /** Every position is moved. */
    static final MoveScope EVERYTHING = new MoveScope(Set.of());

    private final Set<String> notRead;

    private MoveScope(Set<String> notRead) {
        this.notRead = Set.copyOf(notRead);
    }

    /** The positions of the parameters named here stand where the origin has them. */
    static MoveScope leavingStanding(Set<String> parametersTheBodyDoesNotRead) {
        return parametersTheBodyDoesNotRead.isEmpty() ? EVERYTHING
                : new MoveScope(parametersTheBodyDoesNotRead);
    }

    /** Whether a position of {@code axis} may be moved. */
    boolean moves(Axis axis) {
        return moves(axis.path().head());
    }

    /** Whether the value of the parameter {@code name} may be moved. */
    boolean moves(String name) {
        return !notRead.contains(name);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof MoveScope scope && notRead.equals(scope.notRead);
    }

    @Override
    public int hashCode() {
        return notRead.hashCode();
    }

    @Override
    public String toString() {
        return "MoveScope" + notRead;
    }
}
