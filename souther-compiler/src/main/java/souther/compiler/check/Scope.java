package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a body may name where an expression is being typed: the bindings in force, and the
 * declarations a name reaches without one.
 *
 * <p>The two are held apart, and which of them a name reads is decided by what the name denotes. A
 * binding is found by the binding it is, not by how it is spelled — an expansion splices a body
 * written in one scope into another, so a name in the copy would otherwise be answered by whatever
 * the scope it landed in binds under that spelling. That is not shadowing: the copy's names were
 * settled where they were written, and moving the code does not change what they mean.
 *
 * <p>A spelling is still what an author reads, so a name is kept beside each binding for a
 * diagnostic to quote and for a did-you-mean to offer. Nothing is found by it.
 */
public record Scope(Map<BindingId, Binding> bindings, Map<String, Type> declared) {

    /** One binding in force: what it is, and what it is called. */
    public record Binding(String name, Type type) {}

    public static final Scope NONE = new Scope(Map.of(), Map.of());

    /** The bindings a body starts with — a helper's parameters, a declaration's fields. */
    public static Scope of(Map<BindingId, Binding> bindings) {
        return new Scope(Map.copyOf(bindings), Map.of());
    }

    /** The same, with the signatures of the declarations a name may reach without a binding: a
     * recursive helper, which is emitted as a method rather than expanded. */
    public Scope reaching(Map<String, Type> declarations) {
        return new Scope(bindings, Map.copyOf(declarations));
    }

    /**
     * The type of what {@code denotes} names here, or null where nothing here does.
     *
     * <p>{@code reachedBy} is how a declaration is written here, which is the namespace the
     * signatures are keyed by. Which namespace to look in is the denotation's to decide.
     */
    public Type of(ValueName denotes, String reachedBy) {
        return switch (denotes) {
            case ValueName.Local local -> typeOf(local.id());
            case ValueName.Helper _, ValueName.Stdlib _, ValueName.Behavior _ ->
                    declared.get(reachedBy);
            case ValueName.OfType _, ValueName.Builtin _, ValueName.Unresolved _ -> null;
            case null -> null;
        };
    }

    /** The type of one binding, or null where this scope does not hold it. */
    public Type typeOf(BindingId binding) {
        Binding bound = bindings.get(binding);
        return bound == null ? null : bound.type();
    }

    public boolean holds(BindingId binding) {
        return bindings.containsKey(binding);
    }

    /** This scope with {@code binder} bound to {@code type}; the outer one is left as it was. */
    public Scope with(Ast.Binder binder, Type type) {
        return with(binder.id(), binder.name(), type);
    }

    public Scope with(BindingId binding, String name, Type type) {
        Map<BindingId, Binding> next = new LinkedHashMap<>(bindings);
        next.put(binding, new Binding(name, type));
        return new Scope(next, declared);
    }

    /** The same, for several at once. */
    public Scope withAll(Map<BindingId, Binding> more) {
        Map<BindingId, Binding> next = new LinkedHashMap<>(bindings);
        next.putAll(more);
        return new Scope(next, declared);
    }

    /** What the names in force are called — for a diagnostic that offers what the author might have
     * meant, and for nothing else. */
    public List<String> spellings() {
        List<String> names = new ArrayList<>();
        for (Binding bound : bindings.values()) {
            names.add(bound.name());
        }
        names.addAll(declared.keySet());
        return names;
    }

    /** A name-to-type view of the bindings, for a reader that has only a spelling to go on. Two
     * bindings of one spelling collapse, which is why nothing that decides meaning may use it. */
    public Map<String, Type> byName() {
        Map<String, Type> byName = new HashMap<>(declared);
        for (Binding bound : bindings.values()) {
            byName.put(bound.name(), bound.type());
        }
        return byName;
    }
}
