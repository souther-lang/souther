package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a body may name where an expression is being typed: the bindings in force, the declarations
 * an author can name without one, and the signatures a call left standing is typed against.
 *
 * <p>The bindings are held apart from the rest, and which of them a name reads is decided by what
 * the name denotes. A binding is found by the binding it is, not by how it is spelled — an expansion
 * splices a body written in one scope into another, so a name in the copy would otherwise be
 * answered by whatever the scope it landed in binds under that spelling. That is not shadowing: the
 * copy's names were settled where they were written, and moving the code does not change what they
 * mean.
 *
 * <p>{@code visible} and {@code standing} are held apart for a different reason, and it is not about
 * how they are found. Both are consulted by {@link #of}, so either can type a name. Only
 * {@code visible} is a vocabulary — what an author could have written here, which is what a
 * did-you-mean offers. A recursive helper reached under the name the library or another module is
 * reached by is typeable and unwritable at once: {@code List.foldFrom} is behind every list
 * quantifier and no caller outside the reserved namespace may name it. Held in one map, it was
 * offered to authors as something they might have meant.
 *
 * <p>A spelling is still what an author reads, so a name is kept beside each binding for a
 * diagnostic to quote and for a did-you-mean to offer. Nothing is found by it.
 */
public record Scope(Map<BindingId, Binding> bindings, Map<String, Type> visible,
                    Map<String, Type> standing, Substitution decisions) {

    /** A scope with no application's decisions in force over it. */
    public Scope(Map<BindingId, Binding> bindings, Map<String, Type> visible,
                 Map<String, Type> standing) {
        this(bindings, visible, standing, null);
    }

    /**
     * This scope with what {@code decided} has settled in force over it.
     *
     * <p>An expansion's body is read under what that application decided, the way it is read under
     * the bindings its arguments became. A call inside it — a function it was given, reduced where
     * the callee applies it — carries the enclosing application's variables in what was declared of
     * it, and reads them from here rather than deciding them again.
     */
    public Scope deciding(Substitution decided) {
        return new Scope(bindings, visible, standing, decided);
    }

    /** One binding in force: what it is, and what it is called. */
    public record Binding(String name, Type type) {}

    public static final Scope NONE = new Scope(Map.of(), Map.of(), Map.of(), null);

    /** The bindings a body starts with — a helper's parameters, a declaration's fields. */
    public static Scope of(Map<BindingId, Binding> bindings) {
        return new Scope(Map.copyOf(bindings), Map.of(), Map.of(), null);
    }

    /** The same, with the signatures a call left standing is typed against: a recursive helper,
     * which is emitted as a method rather than expanded. Not a vocabulary — the name one is reached
     * by here is not always a name that may be written here. */
    public Scope reaching(Map<String, Type> standingCalls) {
        return new Scope(bindings, visible, Map.copyOf(standingCalls), decisions);
    }

    /** The same, with declarations an author can name here without a binding — an injected behavior
     * a block captured, reached by the name it is declared under. */
    public Scope naming(Map<String, Type> declarations) {
        return new Scope(bindings, Map.copyOf(declarations), standing, decisions);
    }

    /**
     * The type of what {@code denotes} names here, or null where nothing here does.
     *
     * <p>{@code reachedBy} is how a declaration is written here, which is the namespace the
     * signatures are keyed by. Which namespace to look in is the denotation's to decide, and the
     * denotation is also what separates the two: a behavior a block captured is a name its author
     * wrote, and a helper or a library operation reaching here is one a call was left standing on.
     */
    public Type of(ValueName denotes, String reachedBy) {
        return switch (denotes) {
            case ValueName.Local local -> typeOf(local.id());
            case ValueName.Behavior _ -> visible.get(reachedBy);
            case ValueName.Helper _, ValueName.Stdlib _ -> standing.get(reachedBy);
            case ValueName.OfType _, ValueName.Builtin _ -> null;
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
    public Scope with(Hir.Binder binder, Type type) {
        return with(binder.id(), binder.name(), type);
    }

    public Scope with(BindingId binding, String name, Type type) {
        Map<BindingId, Binding> next = new LinkedHashMap<>(bindings);
        next.put(binding, new Binding(name, type));
        return new Scope(next, visible, standing, decisions);
    }

    /** The same, for several at once. */
    public Scope withAll(Map<BindingId, Binding> more) {
        Map<BindingId, Binding> next = new LinkedHashMap<>(bindings);
        next.putAll(more);
        return new Scope(next, visible, standing, decisions);
    }

    /** What the names in force are called — for a diagnostic that offers what the author might have
     * meant, and for nothing else. What a standing call is typed against is not among them: the name
     * such a call is reached by is the one this compilation emits a method under, and offering it
     * would answer a misspelling with a name that cannot be written. */
    public List<String> spellings() {
        List<String> names = new ArrayList<>();
        for (Binding bound : bindings.values()) {
            names.add(bound.name());
        }
        names.addAll(visible.keySet());
        return names;
    }

    /** A name-to-type view of the bindings, for a reader that has only a spelling to go on. Two
     * bindings of one spelling collapse, which is why nothing that decides meaning may use it. What
     * a standing call is typed against is left out for the reason {@link #spellings} leaves it out:
     * this is a view keyed by what was written. */
    public Map<String, Type> byName() {
        Map<String, Type> byName = new HashMap<>(visible);
        for (Binding bound : bindings.values()) {
            byName.put(bound.name(), bound.type());
        }
        return byName;
    }
}
