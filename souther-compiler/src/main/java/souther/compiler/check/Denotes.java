package souther.compiler.check;

import souther.compiler.core.Core;

/**
 * What a binding denotes. A location is somewhere the seeding can have written about and a clause
 * can have named; a term is a value known only by what computes it. Merging those two would put a
 * computed value where a location is expected, which is the shape of a {@code let} answering
 * differently from the expression it was given. A written value is apart from both because what
 * it is has to travel with the name, and nothing is apart because only a term is assigned a form.
 */
sealed interface Denotes {

    /** The key this is known by, or {@code null} where it is known by none. */
    String key();

    /** A place: a parameter, a field chain, or another location a binding was given. */
    record At(Location where) implements Denotes {

        @Override
        public String key() {
            return where.toString();
        }
    }

    /**
     * A value named by the expression that computes it. {@code readable} is true where there is
     * something to say of it however it is reached — a form the numeric domain built, or a rule
     * about how it was made; false where only a guard naming it makes a clause readable against
     * it.
     */
    record Term(String key, boolean readable) implements Denotes {}

    /**
     * A value written out, kept as what was written. There is no guard an author could add about
     * it, so it is never named at a construction; what it is, though, still has to travel with
     * the name, or the same text would fold where it is written and not where it is bound.
     */
    record Written(String key, Core value) implements Denotes {}

    /** Nothing this check can name. */
    record Nothing() implements Denotes {

        @Override
        public String key() {
            return null;
        }
    }
}
