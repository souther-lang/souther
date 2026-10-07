package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Optional;
import java.util.SequencedMap;

/**
 * What a search that composed nothing found out beside its word: everything that keeps a reader
 * from taking the word as the model's.
 *
 * <p>What of this compiler's it met, what the rules about a position's strings left out of what
 * it was offered, whether a candidate it built was turned away for reading back somewhere other
 * than where it was built for, whether a way it had stands under a case of a sum nobody read, and
 * whether a candidate it built had nothing this can write to hand on. Each of them changes what
 * the word may be read as — a figure is a number somebody can raise, an offer short of the rules
 * is a search over less than the position had, a candidate turned away is a search that found
 * what it built standing elsewhere rather than every value refused, a way under a case nobody
 * read is one the search never had, which may have what the others lacked, and a candidate not
 * handed on is one the model took and this compiler did not go on with.
 *
 * <p><b>One value, joined whole.</b> Held as fields a carrier passes on one at a time, each
 * carrier decides which of them to pass, and the one it was not taught is dropped there without a
 * word: a walk that joined what its alternatives met and kept one of them for the rest said a
 * search was complete that was not. Joined with {@link #and}, every part travels together, and a
 * part added later is one every carrier carries.
 *
 * <p><b>Said in one place too.</b> What a search came to reaches a reader as a word with what was
 * found out beside it ({@link #published}), and the word is the one for what was found out
 * ({@link #wordFor}). Put together where it is handed on, each place that hands it on decides
 * which of these to say, and the one it leaves out is dropped at the last step.
 *
 * @param met         what of this compiler's the search met
 * @param offered     what the rules about each position's strings left out of the offer there,
 *                    under the position it is about
 * @param uncertified whether a candidate was turned away for reading back somewhere other than
 *                    where it was built for
 * @param unread      whether a way the search had stands under a case of a sum the row can be
 *                    whose reading stopped, so that the ways it tried are not every way there is
 * @param notHandedOn why a candidate that built had nothing this can write to hand on to a
 *                    container of another parameter, where one had: a value the model took and
 *                    this compiler could not go on with, which is not the model refusing it
 */
record SearchShortfall(CompositionShortfall met,
                       SequencedMap<TermPath, StringOfferShortfall> offered,
                       boolean uncertified, boolean unread, Optional<String> notHandedOn) {

    /** A search that found out nothing of the kind: what it came to is about the model. */
    static final SearchShortfall NONE = new SearchShortfall(CompositionShortfall.NONE,
            new LinkedHashMap<>(), false, false, Optional.empty());

    SearchShortfall {
        offered = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(offered));
    }

    /** What met {@code met} and nothing else. */
    static SearchShortfall of(CompositionShortfall met) {
        return new SearchShortfall(met, new LinkedHashMap<>(), false, false, Optional.empty());
    }

    /** What met {@code met} and was offered short of {@code offered}. */
    static SearchShortfall of(CompositionShortfall met,
                              SequencedMap<TermPath, StringOfferShortfall> offered) {
        return new SearchShortfall(met, offered, false, false, Optional.empty());
    }

    /** Whether there is nothing here, so that the word is all there is to say. */
    boolean nothing() {
        return met.nothing() && offered.isEmpty() && !uncertified && !unread
                && notHandedOn.isEmpty();
    }

    /**
     * What two searches found out together: every figure, every offer short of a rule — one
     * position's short of two rules is short of both — a candidate turned away by either, a way
     * under a case nobody read under either, and a candidate either could not hand on, said as
     * the first of them.
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
        return new SearchShortfall(met.and(other.met()), both, uncertified || other.uncertified(),
                unread || other.unread(),
                notHandedOn.isPresent() ? notHandedOn : other.notHandedOn());
    }

    /** The same, having been turned away building a candidate as well where {@code turnedAway}. */
    SearchShortfall uncertifiedWhere(boolean turnedAway) {
        return turnedAway && !uncertified
                ? new SearchShortfall(met, offered, true, unread, notHandedOn) : this;
    }

    /** The same, with a way under a case nobody read as well where {@code someUnread}. */
    SearchShortfall unreadWhere(boolean someUnread) {
        return someUnread && !unread
                ? new SearchShortfall(met, offered, uncertified, true, notHandedOn) : this;
    }

    /** The same, with a candidate that built and had nothing to hand on, for {@code why}, where
     *  none was already said. */
    SearchShortfall notHandedOn(String why) {
        return notHandedOn.isPresent() ? this
                : new SearchShortfall(met, offered, uncertified, unread, Optional.of(why));
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
     * was refused.
     *
     * <p>Wherever anything here is found out, the word that comes back is not a proof. A proof is
     * the rules leaving nothing over everything there was, and a candidate turned away or a way
     * nobody read is a search that did not have everything — which is what a way left unread says
     * on the way to a cut as well ({@link ReachabilityGap#overEveryWay}).
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
        if (uncertified && said == Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED) {
            return Generator.UnresolvedCombination.Reason.NO_CERTIFIED_WITNESS;
        }
        // Not every candidate refused: one the model took had nothing this could hand on.
        if (notHandedOn.isPresent()
                && said == Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED) {
            return Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE;
        }
        return (uncertified || unread || notHandedOn.isPresent()) && said != null
                && said.provesInfeasible()
                ? Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE : said;
    }

    /**
     * What a search about {@code classes} that came to {@code said} is handed on as: the word for
     * what it found out, the offer it was short of beside the word, and what of this compiler's it
     * met beside that.
     *
     * <p>The one place a search's word leaves for a reader, so that nothing found out is dropped on
     * the way out. A word built from {@code said} alone where this was found out beside it is a
     * proof published over a candidate turned away, or a search complete over a case nobody read.
     */
    CameToNothing published(List<String> classes, Generator.UnresolvedCombination.Reason said,
                            String detail, Optional<String> sentence) {
        return new CameToNothing(new Generator.UnresolvedCombination(classes, wordFor(said),
                detail, toldFor(said, sentence), offered), met);
    }

    /**
     * What is said beside the word for {@code said}: {@code told}, or where nothing was told and
     * what was found out changed the word, why a candidate was not handed on. A reader given only
     * the word that nothing composed one is not told what stopped it.
     */
    Optional<String> toldFor(Generator.UnresolvedCombination.Reason said, Optional<String> told) {
        return told.isEmpty() && wordFor(said) != said ? notHandedOn : told;
    }
}
