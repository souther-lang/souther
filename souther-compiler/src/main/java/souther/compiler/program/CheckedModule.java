package souther.compiler.program;

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
    private final Map<ValueName, CheckedHelper> helperByDeclaration;
    private final List<CheckedData> data;

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
        Map<ValueName, CheckedHelper> byDeclaration = new LinkedHashMap<>();
        for (CheckedHelper helper : this.helpers) {
            CheckedHelper already = byDeclaration.put(helper.declares(), helper);
            if (already != null) {
                // One declaration, two methods for it in one module. A call reaches a declaration
                // and this is what answers with the body, so a second would be a body reached by
                // whichever was filed last with nothing saying the other was here.
                throw new IllegalStateException("`" + name + "` carries `" + helper.declares()
                        + "` twice, as " + already.reachedAs() + " and " + helper.reachedAs());
            }
        }
        this.helperByDeclaration = Map.copyOf(byDeclaration);
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

    /**
     * The method this module carries for the declaration {@code declares}.
     *
     * <p>Asked with what a call reaches, which is the value that call carries — so an output
     * holding one gets to the body by handing this that, and never by writing a name out of an
     * alias, an operation and the module it happens to be emitting.
     *
     * <p>Never a null and never an absence to interpret. Which calls reach a method here is
     * decided before this is made, and a call that reaches one says so
     * ({@link souther.compiler.core.Core.Reaches.AHelper}) — so a declaration this has nothing for
     * is a reader asking about something no call in this module reaches, which is a mistake at the
     * reader rather than a state of the program.
     *
     * @throws IllegalArgumentException where this module carries no method for {@code declares}
     */
    public CheckedHelper helper(ValueName declares) {
        if (declares == null) {
            throw new IllegalArgumentException("a carried method is asked for by what it is a copy"
                    + " of");
        }
        CheckedHelper helper = helperByDeclaration.get(declares);
        if (helper == null) {
            throw new IllegalArgumentException("`" + name + "` carries no method for `" + declares
                    + "`; the methods it carries are " + helpers);
        }
        return helper;
    }

    /**
     * What it declares: what an output emitting this module has to emit.
     *
     * <p>The enumeration and not a way of reaching one. What a given identity is a declaration of is
     * {@link CheckedProgram#declaration}, which answers for the language's own declarations as well
     * — and a module answering it about its own would be that same answer reachable a second way,
     * by the route that has nothing to say about the rest.
     *
     * <p>No order is answered for. Where a declaration stands among the others is a fact about how
     * the module was read rather than one the language decided. The orders that are decided are
     * inside a declaration: the fields a value lays out, and the cases it can be.
     */
    public List<CheckedData> data() {
        return data;
    }

    @Override
    public String toString() {
        return name;
    }
}
