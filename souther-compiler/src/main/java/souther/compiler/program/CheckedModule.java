package souther.compiler.program;

import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
    private final List<CheckedValue> values;
    private final Map<ValueName.Helper, CheckedValue> valueByName;
    private final List<CheckedData> data;
    private final Set<TypeSymbol.AtModule> declaredData;
    private final Set<String> published;

    CheckedModule(String name, List<CheckedBehavior> behaviors, List<CheckedHelper> helpers,
                  List<CheckedValue> values, List<CheckedData> data, Set<String> published) {
        this.name = name;
        this.published = Set.copyOf(published);
        this.behaviors = List.copyOf(behaviors);
        this.helpers = List.copyOf(helpers);
        this.values = List.copyOf(values);
        this.data = List.copyOf(data);
        Map<ValueName.Behavior, CheckedBehavior> byBehavior = new LinkedHashMap<>();
        for (CheckedBehavior behavior : this.behaviors) {
            byBehavior.put(behavior.name(), behavior);
        }
        this.behaviourByName = Map.copyOf(byBehavior);
        Set<TypeSymbol.AtModule> dataNames = new HashSet<>();
        for (CheckedData declaration : this.data) {
            dataNames.add(declaration.name());
        }
        this.declaredData = Set.copyOf(dataNames);
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
        Map<ValueName.Helper, CheckedValue> byName = new LinkedHashMap<>();
        for (CheckedValue value : this.values) {
            if (!value.name().module().equals(name)) {
                // A value runs in the module that declares it and in no other, so a module holding
                // one another module declared would be running it a second time.
                throw new IllegalStateException("`" + name + "` holds the value `" + value.name()
                        + "`, which another module declares");
            }
            if (byName.put(value.name(), value) != null) {
                throw new IllegalStateException("`" + name + "` holds `" + value.name()
                        + "` twice");
            }
            if (byDeclaration.containsKey(value.name())) {
                throw new IllegalStateException("`" + name + "` holds `" + value.name()
                        + "` as a value and carries a method for it as a helper");
            }
        }
        this.valueByName = Map.copyOf(byName);
    }

    /**
     * Whether this module publishes the behavior {@code name}, or keeps it.
     *
     * <p>Asked of the module because that is what the question is: a name being published is this
     * module's surface holding it, and a module is the only thing that can be asked what its
     * surface is. Asked of a definition instead, a definition this module carries and another
     * module declared — which is most of {@link #helpers()} — would answer about whose surface is
     * not said.
     *
     * <p>Of a behavior here. A data is answered the same way by
     * {@link #publicationOf(TypeSymbol.AtModule)}; a value and a helper are answered here when a
     * reader needs each — a question asked of a wider domain than it can answer over would have to
     * answer {@code KEPT} for a name that is not declared at all, which is a different thing and
     * reads as the module having decided it.
     *
     * @throws IllegalArgumentException where this module declares no behavior {@code name}
     */
    public Publication publicationOf(ValueName.Behavior name) {
        if (name == null) {
            throw new IllegalArgumentException("a behavior is asked about by its identity");
        }
        if (!behaviourByName.containsKey(name)) {
            throw new IllegalArgumentException("`" + this.name + "` declares no behavior `" + name
                    + "`, and what another module publishes is that module's answer");
        }
        return publicationOfBaseName(name.name());
    }

    /**
     * Whether this module publishes the data {@code name}, or keeps it.
     *
     * <p>The data counterpart of {@link #publicationOf(ValueName.Behavior)}; see there for why the
     * question is asked of a module and why it stays narrow to the identities a reader has needed.
     *
     * @throws IllegalArgumentException where this module declares no data {@code name}
     */
    public Publication publicationOf(TypeSymbol.AtModule name) {
        if (name == null) {
            throw new IllegalArgumentException("a data is asked about by its identity");
        }
        if (!declaredData.contains(name)) {
            throw new IllegalArgumentException("`" + this.name + "` declares no data `" + name
                    + "`, and what another module publishes is that module's answer");
        }
        return publicationOfBaseName(name.name());
    }

    private Publication publicationOfBaseName(String name) {
        return published.contains(name) ? Publication.PUBLISHED : Publication.KEPT;
    }

    /** What the module is called: what its own declarations are under, and what an import names. */
    public String name() {
        return name;
    }

    /** Its behaviors, in the order they were declared. */
    public List<CheckedBehavior> behaviors() {
        return behaviors;
    }

    /**
     * The whole of what this module's behavior {@code name} was checked to be.
     *
     * <p>Never a null and never an absence to interpret. Which behaviors this module declares is
     * decided before this is made, so a name it has nothing for is a reader asking this module
     * about a behavior of somewhere else — a mistake at the reader rather than a state of the
     * program, and answering it with an absence reads as "no such behavior" for a behavior that
     * exists and is declared elsewhere.
     *
     * <p>What a call to a behavior reaches, wherever it is declared, is
     * {@link CheckedProgram#behavior}. This is for a reader that is emitting this module and wants
     * what only its own compile knows: what the behavior declares of its answer, and what its
     * examples said.
     *
     * @throws IllegalArgumentException where this module declares no behavior {@code name}
     */
    public CheckedBehavior behavior(ValueName.Behavior name) {
        if (name == null) {
            throw new IllegalArgumentException("a behavior is asked for by its identity");
        }
        CheckedBehavior behavior = behaviourByName.get(name);
        if (behavior == null) {
            throw new IllegalArgumentException("`" + this.name + "` declares no behavior `" + name
                    + "`; the behaviors it declares are " + behaviors);
        }
        return behavior;
    }

    /** The methods this module carries for declarations a call was left standing to: its recursions,
     *  and the methods compiled for its rows' values and for the entries of its values. Not its
     *  values, which are {@link #values()}. */
    public List<CheckedHelper> helpers() {
        return helpers;
    }

    /** The values this module builds, each in the one place it runs. */
    public List<CheckedValue> values() {
        return values;
    }

    /**
     * The value {@code name} as the one place it runs.
     *
     * <p>Never a null and never an absence to interpret. A call in this module that reaches one of
     * its values says so ({@link souther.compiler.core.Core.Reaches.AValue}), and a value another
     * module declares is reached through that module's entry and runs there — so a name this has
     * nothing for is a reader asking about a value this module does not build, which is a mistake
     * at the reader rather than a state of the program.
     *
     * @throws IllegalArgumentException where this module builds no value {@code name}
     */
    public CheckedValue value(ValueName.Helper name) {
        if (name == null) {
            throw new IllegalArgumentException("a value is asked for by its identity");
        }
        CheckedValue value = valueByName.get(name);
        if (value == null) {
            throw new IllegalArgumentException("`" + this.name + "` builds no value `" + name
                    + "`; the values it builds are " + values);
        }
        return value;
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
