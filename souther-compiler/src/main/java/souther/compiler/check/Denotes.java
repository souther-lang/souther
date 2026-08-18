package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * What a binding denotes. A location is somewhere the seeding can have written about and a clause
 * can have named; a computed value is known only by the {@link Term} that computes it. Merging those
 * two would put a computed value where a location is expected, which is the shape of a {@code let}
 * answering differently from the expression it was given. A written value is apart from both because
 * what it is has to travel with the name, and nothing is apart because only a computed value is
 * assigned a form.
 *
 * <p>What each is named by is {@link Terms#termOf}'s to say, and not a member here: a place is named
 * by the term standing for it, and the terms of one reading are held together.
 */
sealed interface Denotes {

    /** A place: a parameter, a field chain, or another location a binding was given. */
    record At(Location where) implements Denotes {}

    /**
     * A value named by the expression that computes it.
     *
     * <p>Whether a clause may be read against it is not held here. It was, as a flag decided when the
     * binding was entered, and a flag is a second record of something the expression already answers:
     * {@link Terms#intrinsicallyReadable} asks it of the expression, and what a path has said about
     * the value is {@link Known}'s. A denotation says what a value <em>is</em>; what can be done with
     * it is worked out from that and from what is known, and not stored beside it.
     */
    record Computed(Term term) implements Denotes {}

    /**
     * A value written out, kept as what was written. There is no guard an author could add about
     * it, so it is never named at a construction; what it is, though, still has to travel with
     * the name, or the same text would fold where it is written and not where it is bound.
     */
    record Written(Term term, Core value) implements Denotes {}

    /** Nothing this check can name, and why it can name none of it ({@link Naming}). Kept rather
     * than dropped because the two reasons a value has no name are not one reason: what an injected
     * behavior answered is unnameable, and a shape this compiler has no term for is unfinished. */
    record Nothing(Naming.Unnamed why) implements Denotes {}
}
