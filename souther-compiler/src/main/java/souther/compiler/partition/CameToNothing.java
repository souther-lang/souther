package souther.compiler.partition;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;

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
     * These as the answers they are: each word once, with what every search that came back with it
     * met added up under it.
     *
     * <p><b>The one law for putting two of these together, and every carrier of them applies it.</b>
     * The two halves join differently — a word is what makes two answers one answer, and what was
     * met is information that adds up — and a caller that let the container decide had them joined
     * by whether the whole value was equal. Two searches that came back with one word having met
     * two different figures were then two answers about one thing, and a reader met the same class
     * twice with half the figures apiece.
     *
     * <p>Held to at construction rather than asked of whoever puts a list together. A carrier that
     * holds two of these under one word is a state nothing downstream can read correctly, so it is
     * not a state anything can build — which is what keeps the law from being one more thing a new
     * caller has to know.
     *
     * <p>In the order the words were first met, which is the order a search met them in.
     */
    public static List<CameToNothing> joined(Collection<CameToNothing> all) {
        SequencedMap<Generator.UnresolvedCombination, CompositionShortfall> under =
                new LinkedHashMap<>();
        for (CameToNothing each : all) {
            under.merge(each.why(), each.met(), CompositionShortfall::and);
        }
        List<CameToNothing> out = new ArrayList<>();
        under.forEach((why, met) -> out.add(new CameToNothing(why, met)));
        return List.copyOf(out);
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
