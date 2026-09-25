package souther.compiler.program;

import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
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
    private final List<CheckedValueEntry> valueEntries;
    private final Map<ValueName.Helper, CheckedValueEntry> valueEntryByValue;
    private final List<CheckedData> data;
    private final Set<TypeSymbol.AtModule> declaredData;
    private final Set<String> published;

    CheckedModule(String name, List<CheckedBehavior> behaviors, List<CheckedHelper> helpers,
                  List<CheckedValue> values, List<CheckedValueEntry> valueEntries,
                  List<CheckedData> data, Set<String> published) {
        this.name = name;
        this.published = Set.copyOf(published);
        this.behaviors = List.copyOf(behaviors);
        this.helpers = List.copyOf(helpers);
        this.values = List.copyOf(values);
        this.valueEntries = List.copyOf(valueEntries);
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
        Map<ValueName.Helper, CheckedValueEntry> byEntry = new LinkedHashMap<>();
        for (CheckedValueEntry entry : this.valueEntries) {
            if (!byName.containsKey(entry.value())) {
                // ADR-0074: the entry is for a value this module builds. One that named a value
                // nowhere in `values()` would be an entry with nothing for a call through it to
                // reach.
                throw new IllegalStateException("`" + name + "` holds an entry for `" + entry.value()
                        + "`, which it builds no value for");
            }
            if (byEntry.put(entry.value(), entry) != null) {
                throw new IllegalStateException("`" + name + "` holds an entry for `" + entry.value()
                        + "` twice");
            }
        }
        // ADR-0074, held as one equality rather than as two checks the constructor could agree with
        // itself about arriving at separately: the values with an entry are exactly the values this
        // module publishes — a constant's fold included, since the surface a module offers to Java
        // does not depend on whether a value happens to fold, and never a value this module keeps,
        // which nothing outside it can call through.
        Set<ValueName.Helper> publishedValues = new LinkedHashSet<>();
        for (ValueName.Helper value : byName.keySet()) {
            if (published.contains(value.name())) {
                publishedValues.add(value);
            }
        }
        if (!byEntry.keySet().equals(publishedValues)) {
            throw new IllegalStateException("`" + name + "` publishes " + publishedValues
                    + " and holds an entry for " + byEntry.keySet());
        }
        this.valueEntryByValue = Map.copyOf(byEntry);
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

    /**
     * Whether this module publishes the value {@code value}, or keeps it.
     *
     * <p>The value counterpart of {@link #publicationOf(ValueName.Behavior)}; see there for why the
     * question is asked of a module. Named {@code publicationOfValue} rather than overloaded onto
     * {@code publicationOf}: {@link ValueName.Helper} is also a carried helper's identity
     * ({@link CheckedHelper#declares()}), and a helper's own publication (ADR-0075) is a different
     * question a reader may one day want answered by the same identity type — an overload taken by
     * this one now would leave that question nowhere to go.
     *
     * @throws IllegalArgumentException where this module builds no value {@code value}
     */
    public Publication publicationOfValue(ValueName.Helper value) {
        if (value == null) {
            throw new IllegalArgumentException("a value is asked about by its identity");
        }
        if (!valueByName.containsKey(value)) {
            throw new IllegalArgumentException("`" + this.name + "` builds no value `" + value
                    + "`, and what another module publishes is that module's answer");
        }
        return publicationOfBaseName(value.name());
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
     *  and the methods compiled for its rows' values. Not its values, which are {@link #values()},
     *  and not the entries it publishes for them, which are {@link #valueEntries()}. */
    public List<CheckedHelper> helpers() {
        return helpers;
    }

    /** The values this module builds, each in the one place it runs. */
    public List<CheckedValue> values() {
        return values;
    }

    /**
     * The entries this module publishes, one per value it publishes.
     *
     * <p>Not the value's own body: an entry is the nullary bridge ADR-0074 describes, which another
     * module calls in place of holding a copy of the value. Every published value has one here, a
     * constant's fold included — the invariant this class's constructor holds.
     */
    public List<CheckedValueEntry> valueEntries() {
        return valueEntries;
    }

    /**
     * The entry this module publishes for the value {@code value}.
     *
     * <p>Never a null and never an absence to interpret, the same as {@link #value}: a value this
     * module publishes has an entry by construction, and a value it does not publish is not this
     * method's to answer for — ask {@link #publicationOfValue} first.
     *
     * @throws IllegalArgumentException where this module holds no entry for {@code value}
     */
    public CheckedValueEntry valueEntry(ValueName.Helper value) {
        if (value == null) {
            throw new IllegalArgumentException("an entry is asked for by the value it publishes");
        }
        CheckedValueEntry entry = valueEntryByValue.get(value);
        if (entry == null) {
            throw new IllegalArgumentException("`" + name + "` holds no entry for `" + value
                    + "`; the entries it holds are " + valueEntries);
        }
        return entry;
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
