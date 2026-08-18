package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

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

    /**
     * What a binding means to this check, which is three answers and not one.
     *
     * @param value what it was given, where it was given anything — a fresh location is introduced
     *              rather than given a value, and has none
     * @param subject what a fact about it is about. Handed in rather than worked out from
     *                {@code denotes}: which value this is is {@link Terms}' to say and one thing has
     *                to say it, and a denotation is what a reading may <em>do</em> with the binding.
     *                Read from the denotation, a binding that names an answer would be named by
     *                nothing, and a binding entered as a place would be named by the place — so
     *                refining a value and introducing one could not be told apart
     * @param denotes what a reading may make of it: whether a clause can be read against it, and
     *                what it was written as where that has to travel with the name
     */
    record Means(Core value, FactSubject subject, Denotes denotes) {}

    static Denotations none() {
        return new Denotations(Map.of());
    }

    /** What a fact about {@code binding} is about, or null where nothing entered it. */
    FactSubject subject(BindingId binding) {
        Means given = bound.get(binding);
        return given == null ? null : given.subject();
    }

    /** What {@code binding} denotes, which is nothing where nothing entered it. */
    Denotes of(BindingId binding) {
        Means given = bound.get(binding);
        return given != null ? given.denotes()
                : new Denotes.Nothing(new Naming.Opaque(Naming.Reason.A_BINDING_STANDS_FOR_NOTHING));
    }

    /** The value {@code binding} was given, or null where nothing recorded one. */
    Core valueOf(BindingId binding) {
        Means given = bound.get(binding);
        return given == null ? null : given.value();
    }

    /** {@code binding} entered as the location it is: somewhere the seeding can write about, which
     * nothing else names. Entering it is half of introducing one — what its type guarantees is the
     * other half, and {@link InvariantChecker#enter} is where the two are one act.
     *
     * <p>{@code subject} is the place it is, asked of {@link Terms#placeSubject}. Building it here
     * would make this an identity factory as well as an environment, and a second place that decides
     * which value something is is a second answer to keep agreeing with the first. */
    Denotations location(BindingId binding, FactSubject subject) {
        return with(binding, new Means(null, subject, new Denotes.At(Location.of(binding))));
    }

    /** The same, for bindings that stand for themselves rather than for a value the walk reached —
     * a declaration's own fields, where its invariant is read on its own. */
    Denotations locations(Collection<BindingId> bindings, Function<BindingId, FactSubject> places) {
        Denotations out = this;
        for (BindingId binding : bindings) {
            out = out.location(binding, places.apply(binding));
        }
        return out;
    }

    Denotations binding(BindingId binding, Core value, FactSubject subject, Denotes denotes) {
        return with(binding, new Means(value, subject, denotes));
    }

    private Denotations with(BindingId binding, Means means) {
        Map<BindingId, Means> next = new HashMap<>(bound);
        next.put(binding, means);
        return new Denotations(Map.copyOf(next));
    }
}
