package souther.compiler.query;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.AnalysisBody;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * The behaviors a behavior calls, directly or through another behavior, in the order the calls are
 * met.
 *
 * <p>A call is read where {@link CallExampleSeeds} reads one, off the same body, so the two never
 * disagree about what a behavior calls. A behavior of another module is followed into that
 * module's own bodies; one the language declares has no rows of a model to take, and is not
 * followed.
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
            AnalysisBody body = checked == null ? null : checked.analysisBodies().get(each.name());
            if (body == null) {
                continue;
            }
            List<AnOperationApplied> calls = new ArrayList<>();
            CallExampleSeeds.collect(body.core(), called -> !called.isDeclaredByLanguage(), calls);
            for (AnOperationApplied call : calls) {
                if (call.operation() instanceof ValueName.Behavior called && seen.add(called)) {
                    reached.add(called);
                    pending.addLast(called);
                }
            }
        }
        return List.copyOf(reached);
    }
}
