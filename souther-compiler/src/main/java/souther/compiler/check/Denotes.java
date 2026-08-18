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
     * A value written out. There is no guard an author could add about it, so it is never named at a
     * construction.
     *
     * <p>What was written is not held here. A name is what it was given, and the walk records that
     * one binding at a time, so the text is however many names away it was written and following
     * what a name was given reaches it ({@link Terms#writtenValue}). Held here as well, the same
     * fact was written down twice — once as what the binding stands for and once as the text a
     * reading of it folds — and the two had to be kept agreeing wherever a binding is entered.
     */
    record Written(Term term) implements Denotes {}

    /**
     * Nothing this check can name.
     *
     * <p>Why it can name none of it is {@link Naming}'s, and it is asked there. The two reasons are
     * not one reason — what an injected behavior answered is unnameable, and a shape this compiler
     * has no term for is unfinished — and that distinction earns its place where the naming is done,
     * where telling them apart is what stops an analysis this compiler could not follow from reading
     * as one it followed to nothing (#722). Carried past that point it was read by no one: a
     * distinction is worth holding where something asks it, and a reader that wants the reason has
     * to be given one, which is a question of its own to introduce with whatever asks it.
     */
    record Nothing() implements Denotes {}
}
