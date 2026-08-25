package souther.compiler.program;

import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * One module the compiler checked, as an output outside this compiler reads it.
 *
 * <p>A class and not a record, for the reason {@link CheckedBehavior} is one: what a checked module
 * is known to be will grow — its invariants, what its examples said — and each of those arrives as
 * a question a reader asks rather than as a place in a constructor.
 */
public final class CheckedModule {

    private final String name;
    private final List<CheckedBehavior> behaviors;
    private final Map<ValueName.Behavior, CheckedBehavior> behaviourByName;
    private final List<CheckedHelper> helpers;
    private final Map<ValueName.Helper, CheckedHelper> helperByName;
    private final List<CheckedData> data;
    private final Map<TypeSymbol.AtModule, CheckedData> dataByName;

    CheckedModule(String name, List<CheckedBehavior> behaviors, List<CheckedHelper> helpers,
                  List<CheckedData> data) {
        this.name = name;
        this.behaviors = List.copyOf(behaviors);
        this.helpers = List.copyOf(helpers);
        this.data = List.copyOf(data);
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
        Map<TypeSymbol.AtModule, CheckedData> byData = new LinkedHashMap<>();
        for (CheckedData declared : this.data) {
            byData.put(declared.name(), declared);
        }
        this.dataByName = Map.copyOf(byData);
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

    /**
     * What it declares.
     *
     * <p>No order is answered for. A declaration is reached by its name —
     * {@link #data(TypeSymbol.AtModule)} — and where one stands among the others is a fact about
     * how the module was read rather than one the language decided. The orders that are decided
     * are inside a declaration: the fields a value lays out, and the cases it can be.
     */
    public List<CheckedData> data() {
        return data;
    }

    /**
     * The declaration {@code name} reaches, or null where it is not one of this module's.
     *
     * <p>Reached through the module that declares it, as a behavior and a helper are. A name
     * carries the module it was declared by, so a reader holding one asks that module — and where
     * this compile did not check it, {@link CheckedProgram#module} has already answered null and the
     * two absences stay apart.
     */
    public CheckedData data(TypeSymbol.AtModule name) {
        return dataByName.get(name);
    }

    @Override
    public String toString() {
        return name;
    }
}
