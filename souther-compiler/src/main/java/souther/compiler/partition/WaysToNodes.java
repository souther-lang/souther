package souther.compiler.partition;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

/**
 * The way the walk was on when it evaluated each node of a fork's condition: every condition that
 * stood on the way to the node, once for each time the walk reached it.
 *
 * <p>What the walk says and nobody else: it is the walk that meets the right of an {@code &&} under
 * the left coming out true, the body of a closure under what stands in it, and an arm under what the
 * arm proves. A reader that wants to know whether a part of a condition is evaluated at all asks
 * for the part's way here, so that the answer is the one the comparisons of the same walk were read
 * under and no second account of where evaluation goes.
 *
 * <p><b>A list of ways and not one.</b> A node is reached more than once when a closure is read on
 * each of its applications or a helper at each of its calls, and what stood on the way differs
 * between them. A part is evaluated where any of them is, so a reader holding the ways is asked
 * whether some one of them may be taken, and a way recorded over another's would answer for the
 * wrong run.
 *
 * <p><b>Only within a fork's condition.</b> Those are the nodes a part of a fork can be, and the
 * walk meets every other node as well.
 *
 * <p>Complete once the walk is, and shared by every reading of the body it is made for, as the other
 * gatherings of the walk are.
 */
final class WaysToNodes {

    private final Map<Core, List<List<OnTheWay>>> ways = new IdentityHashMap<>();
    private int withinACondition;

    /** That the walk is about to enter a fork's condition. */
    void enteringACondition() {
        withinACondition++;
    }

    /** That the walk has left the condition it entered last. */
    void leavingACondition() {
        withinACondition--;
    }

    /** That the walk reached {@code node} on {@code assumed}. */
    void reached(Core node, List<OnTheWay> assumed) {
        if (withinACondition > 0) {
            ways.computeIfAbsent(Core.withoutStanding(node), _ -> new ArrayList<>(1))
                    .add(assumed);
        }
    }

    /** Each way the walk reached {@code node} on, or none where it never did. */
    List<List<OnTheWay>> to(Core node) {
        List<List<OnTheWay>> found = ways.get(Core.withoutStanding(node));
        return found == null ? List.of() : List.copyOf(found);
    }
}
