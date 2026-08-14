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
     * A value named by the expression that computes it. {@code readable} is true where there is
     * something to say of it however it is reached — a form the numeric domain built, or a rule
     * about how it was made; false where only a guard naming it makes a clause readable against
     * it.
     */
    record Computed(Term term, boolean readable) implements Denotes {}

    /**
     * A value written out, kept as what was written. There is no guard an author could add about
     * it, so it is never named at a construction; what it is, though, still has to travel with
     * the name, or the same text would fold where it is written and not where it is bound.
     */
    record Written(Term term, Core value) implements Denotes {}

    /** Nothing this check can name. */
    record Nothing() implements Denotes {}
}
