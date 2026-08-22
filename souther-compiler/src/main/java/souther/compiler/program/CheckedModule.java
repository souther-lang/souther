package souther.compiler.program;

import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * One module the compiler checked, as an output outside this compiler reads it.
 *
 * <p>A class and not a record, for the reason {@link CheckedBehavior} is one: what a checked module
 * is known to be will grow — its declared shapes, its invariants, what its examples said — and each
 * of those arrives as a question a reader asks rather than as a place in a constructor.
 */
public final class CheckedModule {

    private final String name;
    private final List<CheckedBehavior> behaviors;
    private final Map<ValueName.Behavior, CheckedBehavior> behaviourByName;
    private final List<CheckedHelper> helpers;
    private final Map<ValueName.Helper, CheckedHelper> helperByName;

    CheckedModule(String name, List<CheckedBehavior> behaviors, List<CheckedHelper> helpers) {
        this.name = name;
        this.behaviors = List.copyOf(behaviors);
        this.helpers = List.copyOf(helpers);
        Map<ValueName.Behavior, CheckedBehavior> byBehavior = new LinkedHashMap<>();
        for (CheckedBehavior behavior : this.behaviors) {
            byBehavior.put(behavior.name(), behavior);
        }
        this.behaviourByName = Map.copyOf(byBehavior);
        Map<ValueName.Helper, CheckedHelper> byHelper = new LinkedHashMap<>();
        for (CheckedHelper helper : this.helpers) {
            byHelper.put(helper.name(), helper);
        }
        this.helperByName = Map.copyOf(byHelper);
    }

    /** What the module is called: what its own declarations are under, and what an import names. */
    public String name() {
        return name;
    }

    /** Its behaviors, in the order they were declared. */
    public List<CheckedBehavior> behaviors() {
        return behaviors;
    }

    /** The behavior {@code name} reaches, or null where it is not one of this module's. */
    public CheckedBehavior behavior(ValueName.Behavior name) {
        return behaviourByName.get(name);
    }

    /** The helpers this module emits as definitions of their own. */
    public List<CheckedHelper> helpers() {
        return helpers;
    }

    /** The helper {@code name} reaches, or null where it is not one of this module's. */
    public CheckedHelper helper(ValueName.Helper name) {
        return helperByName.get(name);
    }

    @Override
    public String toString() {
        return name;
    }
}
