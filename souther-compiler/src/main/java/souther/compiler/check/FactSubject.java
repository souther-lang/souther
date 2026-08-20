package souther.compiler.check;

/**
 * What a fact is about: the subject a constraint, a predicate or a clause is read against.
 *
 * <p>A {@link Term} is how a value is built. This is a term put forward as something facts may be
 * filed under, and the two are separate types so that the second cannot be reached by accident: a
 * key built for the symbolic domain to read is not thereby a key the fact set may speak of, and the
 * places that had quietly used one as the other are the places this boundary is for.
 *
 * <p>Which two values are one is decided in the algebra, not here and not by any reader. A structural
 * term is equal to its twin, so two writings of a place, or of an operation over places, are one
 * subject without anything being asked. An evaluation nothing may share is a {@code Term.Shape#EVALUATION}
 * leaf, equal to itself and to nothing else — and because it is a leaf of the same algebra, what is
 * built over it composes: {@code length(E)} written twice is one subject, and {@code length(E1)} and
 * {@code length(E2)} are two.
 *
 * <p>That is the separation this type exists for, and it is a rule about constructors rather than a
 * property of subjects. A pure operation decides its result from the identity of its operands; an
 * evaluation that reaches outside the language decides nothing and takes a fresh atom. Asking a
 * subject whether it is shareable would be asking the wrong thing of the wrong half — the question
 * belongs to whoever built it, and it was answered there.
 *
 * <p>Held two ways before this: a subject was a term, whose equality is structural, so anything given
 * a subject was thereby declared shareable and a value that could be named but not shared had nowhere
 * to be. That is why a call to a {@code behavior} was named by nothing, and why a construction built
 * from its answer was neither proved nor refuted nor reported (#819).
 */
record FactSubject(Term identity) {

    FactSubject {
        java.util.Objects.requireNonNull(identity, "a subject is something to point at");
    }

    /** The subject the value built like {@code identity} is. Null in, null out, so a caller with
     * nothing to name stays a caller with nothing to name. */
    static FactSubject of(Term identity) {
        return identity == null ? null : new FactSubject(identity);
    }

    /** What to call this where a message names it. For a reader, not for equality. */
    String rendered() {
        return identity.rendered();
    }
}
