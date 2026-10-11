package souther.compiler.check;

import souther.compiler.types.ValueName;

import java.util.Objects;
import java.util.Optional;

/**
 * The body of a recursive helper as a call of it is read, with what it walks: a list by its head
 * ({@link RecursionOverAList}), or else a node and the nodes its calls go to
 * ({@link RecursionOverATree}). Each is said once of the body, however many calls read it.
 *
 * @param body   the body as a call of the helper is read
 * @param walk   the list it walks by its head, where it walks one
 * @param search the calls it makes of itself on another node, where it walks no list and makes
 *               some
 */
public record ARecursion(CalledBody body, Optional<RecursionOverAList> walk,
                         Optional<RecursionOverATree> search) {

    public ARecursion {
        Objects.requireNonNull(body, "a recursion has a body");
        Objects.requireNonNull(walk, "it walks a list or not");
        Objects.requireNonNull(search, "it searches from a node or not");
    }

    /** {@code body}, the body of {@code self}, with what it walks. */
    public static ARecursion of(ValueName.Helper self, CalledBody body) {
        RecursionOverAList walk = RecursionOverAList.of(self, body);
        return new ARecursion(body, Optional.ofNullable(walk), walk != null ? Optional.empty()
                : Optional.ofNullable(RecursionOverATree.of(self, body)));
    }
}
