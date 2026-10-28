package souther.compiler.query;

import souther.compiler.core.Core;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The behaviors a behavior calls, directly or through another behavior, in the order the calls are
 * met.
 *
 * <p>Read off the elaborated bodies, the same trees a run goes through, so a call is one here where
 * a run makes it. A behavior of another module is followed into that module's own bodies. A behavior
 * the language declares has no rows of a model to take, and is not followed.
 */
final class CalledBehaviors {

    private CalledBehaviors() {}

    static List<ValueName.Behavior> of(Db db, String module, String behavior) {
        Set<ValueName.Behavior> reached = new LinkedHashSet<>();
        ValueName.Behavior start = new ValueName.Behavior(module, behavior);
        Deque<ValueName.Behavior> pending = new ArrayDeque<>(List.of(start));
        Set<ValueName.Behavior> seen = new LinkedHashSet<>(pending);
        while (!pending.isEmpty()) {
            ValueName.Behavior each = pending.removeFirst();
            Bodies.Elaborated checked = db.ask(new Bodies.Observable(each.module())).value();
            Core body = checked == null ? null : checked.behaviorBodies().get(each.name());
            if (body == null) {
                continue;
            }
            for (ValueName.Behavior called : callsIn(body)) {
                if (seen.add(called)) {
                    reached.add(called);
                    pending.addLast(called);
                }
            }
        }
        return List.copyOf(reached);
    }

    private static Set<ValueName.Behavior> callsIn(Core body) {
        Set<ValueName.Behavior> out = new LinkedHashSet<>();
        collect(body, out);
        return out;
    }

    private static void collect(Core e, Set<ValueName.Behavior> out) {
        if (e instanceof Core.Call call && call.fn() instanceof Core.Reached reached
                && reached.denotes() instanceof ValueName.Behavior called
                && !called.isDeclaredByLanguage()) {
            out.add(called);
        }
        Core.forEachChild(e, child -> collect(child, out));
    }
}
