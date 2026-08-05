package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.HashMap;
import java.util.Map;

/**
 * What the body's bindings mean where the walk is.
 *
 * <p>A binding given a location <em>is</em> that location — the rule {@link Location} carries for
 * a newtype's {@code .value}, read here of a binding instead of a field. It is what lets a
 * construction survive being moved into a helper: an expansion binds each argument and answers
 * the parameter's reads with that binding (see {@link HelperInliner}), so without it the body of
 * a helper taking a record names locations the seeding never wrote, and everything an input's
 * type guarantees stops at the call.
 *
 * <p>Nothing here is ever taken away. A binding is what it is, and a second binding of the same
 * spelling is a second binding, so a fact about the first stays true of the first and nothing
 * reads it under the second.
 */
record Denotations(Map<BindingId, Bound> bound) {

    /** What a binding was given: the value it was bound to, and what that value denotes. */
    record Bound(Core value, Denotes denotes) {}

    static Denotations none() {
        return new Denotations(Map.of());
    }

    /** What {@code binding} denotes, which is the location it is unless it was given something
     * else. */
    Denotes of(BindingId binding) {
        Bound given = bound.get(binding);
        return given != null ? given.denotes() : new Denotes.At(Location.of(binding));
    }

    /** The value {@code binding} was given, or null where nothing recorded one. */
    Core valueOf(BindingId binding) {
        Bound given = bound.get(binding);
        return given == null ? null : given.value();
    }

    Denotations binding(BindingId binding, Core value, Denotes denotes) {
        Map<BindingId, Bound> next = new HashMap<>(bound);
        next.put(binding, new Bound(value, denotes));
        return new Denotations(Map.copyOf(next));
    }
}
