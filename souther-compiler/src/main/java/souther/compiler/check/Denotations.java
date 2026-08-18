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
 * <p>A binding given a location may be read against as that location — the rule {@link Location}
 * carries for a newtype's {@code .value}, read here of a binding instead of a field. It is what lets
 * a construction survive being moved into a helper: an expansion binds each argument and answers
 * the parameter's reads with that binding (see {@link HelperInliner}), so without it the body of
 * a helper taking a record names locations the seeding never wrote, and everything an input's
 * type guarantees stops at the call.
 *
 * <p>Being a place says what may be done with a binding and not which value it is. A {@code match}
 * arm opens the value the scrutinee already was, and it is a place all the same — so what it denotes
 * and what it is about are recorded apart, and neither is read off the other.
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
     * What a binding means to this check: the questions asked of it, each with an answer of its own.
     *
     * <p>Held apart because they are apart. One classification stood here and said which of four
     * kinds a binding was, and the four were not one question with four answers: measured over every
     * read of a binding, each kind was one combination of these, and a reader testing one kind was
     * reading what the other kinds had left over. Taking a kind away then widened what that reader
     * read, without the reader changing (#824).
     *
     * <p>Nothing here says which combinations may occur. Four of them do, and those four are the
     * kinds this replaces, but that is what the corpus holds rather than a rule about bindings: a
     * {@code match} arm opening text written into the source is a place whose value was written, and
     * refusing one here would refuse a program for the shape of a record.
     *
     * @param value what it was given, where it was given anything — a place introduced with nothing
     *              behind it has none, and following this is how what was written is found
     * @param subject what a fact about it is about. Handed in rather than worked out from anything
     *                here: which value this is is {@link Terms}' to say and one thing has to say it
     * @param location where it is, or null where it is not a place. What the seeding writes about
     *                 and what a clause may be read against
     * @param term what the term grammar names it by, or null where it names it by nothing
     */
    record Means(Core value, FactSubject subject, Location location, Term term) {

        Means {
            // Every binding this holds is one something is known about. A binding entered without a
            // subject would be read back as one nothing entered, which takes an atom per occurrence
            // — so one value read twice would be two subjects, which is what a subject is for.
            java.util.Objects.requireNonNull(subject, "a binding entered is a binding to be about");
        }
    }

    static Denotations none() {
        return new Denotations(Map.of());
    }

    /** What a fact about {@code binding} is about, or null where nothing entered it. */
    FactSubject subject(BindingId binding) {
        Means given = bound.get(binding);
        return given == null ? null : given.subject();
    }

    /** Where {@code binding} is, or null where it is not a place. */
    Location locationOf(BindingId binding) {
        Means given = bound.get(binding);
        return given == null ? null : given.location();
    }

    /** What the term grammar names {@code binding} by, or null where it names it by nothing. */
    Term termOf(BindingId binding) {
        Means given = bound.get(binding);
        return given == null ? null : given.term();
    }


    /** The value {@code binding} was given, or null where nothing recorded one. */
    Core valueOf(BindingId binding) {
        Means given = bound.get(binding);
        return given == null ? null : given.value();
    }

    /** {@code binding} entered as a place: somewhere the seeding can write about, standing for no
     * value the walk reached. Entering it is half of introducing one — what its type guarantees is
     * the other half, and {@link InvariantChecker#enter} is where the two are one act.
     *
     * <p>{@code subject} is handed in and not worked out. Building it here would make this an
     * identity factory as well as an environment, and a second place that decides which value
     * something is is a second answer to keep agreeing with the first. Usually it is the place the
     * binding is ({@link Terms#placeSubject}); an arm opening an optional hands what that optional
     * holds. */
    Denotations location(BindingId binding, FactSubject subject) {
        return with(binding, new Means(null, subject, Location.of(binding), null));
    }

    /**
     * {@code binding} entered as a place that stands for {@code value}: what a {@code match} arm
     * opens where the value it opened is one the walk already reached.
     *
     * <p>All three answers at once, and they are not the same answer. It is that value — so a reader
     * following what a name was given reaches whatever produced it, which is how a rule declared
     * about an answer is found through however many names the answer went by. It is about that
     * value — so a fact taken under either is a fact about one thing. And it is a place — so a clause
     * may be read against it and the seeding writes about it, which the value it opens, being an
     * answer, is not.
     *
     * <p>Left out, the middle one alone was moved and the first stayed as it was when an arm
     * introduced a value of its own: the name was about the answer while standing for nothing, so a
     * {@code match} over what an outer arm bound could not find the call underneath it.
     */
    Denotations opened(BindingId binding, Core value, FactSubject subject) {
        return with(binding, new Means(value, subject, Location.of(binding), null));
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

    Denotations binding(BindingId binding, Core value, FactSubject subject, Location location,
                        Term term) {
        return with(binding, new Means(value, subject, location, term));
    }

    private Denotations with(BindingId binding, Means means) {
        Map<BindingId, Means> next = new HashMap<>(bound);
        next.put(binding, means);
        return new Denotations(Map.copyOf(next));
    }
}
