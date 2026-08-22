package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.HashSet;
import java.util.Set;

/**
 * Which of a body's bindings something reads.
 *
 * <p>How a body is asked whether a value it computes reaches the answer. Every other place a value
 * stands in a {@link Core} is consumed by whatever it stands in — a condition decides a fork, an
 * operand is combined, an argument is handed over, a field becomes part of a value, a tail is what
 * the body answers with — so the one way to compute a value and read none of it is to bind it to a
 * name nothing reads.
 *
 * <p><b>An approximation, and one that over-reports.</b> Reads are counted wherever they are written,
 * including inside a binding that is itself never read: {@code let a = t < 1} bound in turn to a
 * {@code b} nothing reads leaves {@code a} counted as read. Telling those apart is a fixed point, and
 * what it would take away is a chain of dead bindings — so this stops one step short and says so.
 * The direction is deliberate: a value counted as read that is not leaves a rule stated about a
 * behavior that does not state it, which the author can see in their own body; a value counted as
 * unread that is read takes a rule of the model out of the report with nothing said, which they
 * cannot.
 */
final class LiveFlow {

    private final Set<BindingId> read;

    private LiveFlow(Set<BindingId> read) {
        this.read = read;
    }

    /** The bindings {@code body} reads, wherever in it they are read. */
    static LiveFlow of(Core body) {
        Set<BindingId> read = new HashSet<>();
        walk(body, read);
        return new LiveFlow(read);
    }

    private static void walk(Core e, Set<BindingId> read) {
        if (e instanceof Core.Read name && name.binding() != null) {
            read.add(name.binding());
        }
        Core.forEachChild(e, child -> walk(child, read));
    }

    /** Whether anything reads the name {@code let} binds. */
    boolean reads(Core.LetIn let) {
        return read.contains(let.binder().binding());
    }
}
