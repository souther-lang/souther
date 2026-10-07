package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.SequencedMap;

/**
 * What a search that composed nothing found out beside its word: everything that keeps a reader
 * from taking the word as the model's.
 *
 * <p>What of this compiler's it met, what the rules about a position's strings left out of what
 * it was offered, and whether a candidate it built was turned away for reading back somewhere other
 * than where it was built for. Each of them changes what the word may be read as — a figure is a
 * number somebody can raise, an offer short of the rules is a search over less than the position
 * had, and a candidate turned away is a search that found what it built standing elsewhere rather
 * than every value refused.
 *
 * <p><b>One value, joined whole.</b> Held as fields a carrier passes on one at a time, each
 * carrier decides which of them to pass, and the one it was not taught is dropped there without a
 * word: a walk that joined what its alternatives met and kept one of them for the rest said a
 * search was complete that was not. Joined with {@link #and}, every part travels together, and a
 * part added later is one every carrier carries.
 *
 * @param met         what of this compiler's the search met
 * @param offered     what the rules about each position's strings left out of the offer there,
 *                    under the position it is about
 * @param uncertified whether a candidate was turned away for reading back somewhere other than
 *                    where it was built for
 */
record SearchShortfall(CompositionShortfall met,
                       SequencedMap<TermPath, StringOfferShortfall> offered,
                       boolean uncertified) {

    /** A search that found out nothing of the kind: what it came to is about the model. */
    static final SearchShortfall NONE = new SearchShortfall(CompositionShortfall.NONE,
            new LinkedHashMap<>(), false);

    SearchShortfall {
        offered = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(offered));
    }

    /** What met {@code met} and nothing else. */
    static SearchShortfall of(CompositionShortfall met) {
        return new SearchShortfall(met, new LinkedHashMap<>(), false);
    }

    /** What met {@code met} and was offered short of {@code offered}. */
    static SearchShortfall of(CompositionShortfall met,
                              SequencedMap<TermPath, StringOfferShortfall> offered) {
        return new SearchShortfall(met, offered, false);
    }

    /** Whether there is nothing here, so that the word is all there is to say. */
    boolean nothing() {
        return met.nothing() && offered.isEmpty() && !uncertified;
    }

    /**
     * What two searches found out together: every figure, every offer short of a rule — one
     * position's short of two rules is short of both — and a candidate turned away by either.
     */
    SearchShortfall and(SearchShortfall other) {
        if (other.nothing()) {
            return this;
        }
        if (nothing()) {
            return other;
        }
        SequencedMap<TermPath, StringOfferShortfall> both = new LinkedHashMap<>(offered);
        other.offered().forEach((at, gap) -> both.merge(at, gap, StringOfferShortfall::and));
        return new SearchShortfall(met.and(other.met()), both, uncertified || other.uncertified());
    }

    /** The same, having been turned away building a candidate as well where {@code turnedAway}. */
    SearchShortfall uncertifiedWhere(boolean turnedAway) {
        return turnedAway && !uncertified ? new SearchShortfall(met, offered, true) : this;
    }

    /**
     * The word for a search that came to {@code said} having found out this.
     *
     * <p>Said in one place because it is one rule, read the way the outcomes of one search already
     * read it. A figure's word where a figure stopped it, and the word for what this compiler does
     * not write where it ran to the end of that: either is the search being short of the question,
     * whatever it came to on the way. Short of those, an offer short of the rules makes what came to
     * nothing over it a search over less than the position had. And a search whose candidates were
     * refused, one of which was turned away for standing elsewhere, did not show that every value
     * was refused. Wherever anything here is found out, the word that comes back is not a proof.
     */
    Generator.UnresolvedCombination.Reason wordFor(Generator.UnresolvedCombination.Reason said) {
        if (!met.figures().isEmpty()) {
            return Generator.UnresolvedCombination.Reason.wordFor(met.figures());
        }
        if (!met.nothing()) {
            return Generator.UnresolvedCombination.Reason.THE_SEARCH_LEFT_SOMETHING_UNTRIED;
        }
        if (!offered.isEmpty()) {
            return Generator.UnresolvedCombination.Reason.NOT_ALL_CANDIDATES_COULD_BE_OFFERED;
        }
        if (!uncertified) {
            return said;
        }
        if (said == Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED) {
            return Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS;
        }
        // A proof is a word nothing was found out beside: one beside a candidate turned away is
        // a search that composed nothing, and no more.
        return said != null && said.provesInfeasible()
                ? Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE : said;
    }
}
