package souther.compiler.partition;

/**
 * What a search that composed nothing came back with.
 *
 * <p>Its word, and what of this compiler's it met on the way to that word. The two travel as one
 * value because they are one answer: the word says the question is open, and only what was met says
 * whether a number somebody raises reaches it. Handed on separately, one of them arrives and the
 * other is read for the first and dropped — which is how a search this compiler ended came to reach
 * an author as work they had to do, with nothing in it to act on.
 *
 * <p>Held beside the word rather than inside it, the way every other stop in this compiler holds
 * it. The word such a search comes back with is the figures' to say wherever figures stopped it
 * ({@link Generator.UnresolvedCombination.Reason#wordFor}), so a word that carried them would be
 * one answer kept twice and free to part from itself.
 *
 * @param why what the search says, in the words a report prints
 * @param met what of this compiler's it met, and nothing where it met nothing
 */
public record CameToNothing(Generator.UnresolvedCombination why, CompositionShortfall met) {

    public CameToNothing {
        if (why == null) {
            throw new IllegalArgumentException("a search that came to nothing says what happened");
        }
        if (met == null) {
            throw new IllegalArgumentException(
                    "a search says what of this compiler's it met, or that it met none: " + why);
        }
    }

    /**
     * One that met nothing of this compiler's on the way.
     *
     * <p>Named rather than left as the shorter of two constructors, so that a caller saying it is
     * saying it. A search that met a figure and was written this way is the figure dropped again,
     * and the difference between the two spellings is what a reader is asked to do about the
     * answer.
     */
    public static CameToNothing metNothing(Generator.UnresolvedCombination why) {
        return new CameToNothing(why, CompositionShortfall.NONE);
    }
}
