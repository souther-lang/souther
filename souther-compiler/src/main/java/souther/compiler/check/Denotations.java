package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.Collection;
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
 * <p>Every binding the walk reads is one it entered. A binding nobody entered means nothing here,
 * and a clause naming one is left to the run-time check — where answering it with a location
 * instead would name a place the seeding never wrote about, so the clause would be owed and
 * nothing would establish it. Which is a warning an author cannot clear, on a value they never
 * introduced.
 *
 * <p>Nothing here is ever taken away. A binding is what it is, and a second binding of the same
 * spelling is a second binding, so a fact about the first stays true of the first and nothing
 * reads it under the second.
 */
record Denotations(Map<BindingId, Means> bound) {

    /** What a binding means to this check: what it denotes, and the value it was given where it was
     * given one — a fresh location is introduced rather than given anything, and has none. */
    record Means(Core value, Denotes denotes) {}

    static Denotations none() {
        return new Denotations(Map.of());
    }

    /** What {@code binding} denotes, which is nothing where nothing entered it. */
    Denotes of(BindingId binding) {
        Means given = bound.get(binding);
        return given != null ? given.denotes() : new Denotes.Nothing();
    }

    /** The value {@code binding} was given, or null where nothing recorded one. */
    Core valueOf(BindingId binding) {
        Means given = bound.get(binding);
        return given == null ? null : given.value();
    }

    /** {@code binding} entered as the location it is: somewhere the seeding can write about, which
     * nothing else names. Entering it is half of introducing one — what its type guarantees is the
     * other half, and {@link InvariantChecker#enter} is where the two are one act. */
    Denotations location(BindingId binding) {
        return with(binding, new Means(null, new Denotes.At(Location.of(binding))));
    }

    /** The same, for bindings that stand for themselves rather than for a value the walk reached —
     * a declaration's own fields, where its invariant is read on its own. */
    Denotations locations(Collection<BindingId> bindings) {
        Denotations out = this;
        for (BindingId binding : bindings) {
            out = out.location(binding);
        }
        return out;
    }

    Denotations binding(BindingId binding, Core value, Denotes denotes) {
        return with(binding, new Means(value, denotes));
    }

    private Denotations with(BindingId binding, Means means) {
        Map<BindingId, Means> next = new HashMap<>(bound);
        next.put(binding, means);
        return new Denotations(Map.copyOf(next));
    }
}
