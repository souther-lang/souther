package souther.compiler.partition;

import souther.compiler.publish.PublicationOrders;

import java.util.Comparator;
import java.util.List;
import java.util.Optional;

/**
 * What several alternatives for one choice came to, where none of them composed — said once, over
 * every one of them.
 *
 * <p>The ways of writing a row under the cases of a sum, the ways a stated value is written, the
 * values of a parameter a later one turns on: each is a walk over alternatives, and what it comes
 * to when none composes is one answer about all of them. Kept as the answer of one of them, the
 * rest are dropped — a figure one of them stopped at is a number nobody is told to raise, an offer
 * one of them was short of is a search said to be complete, and a proof one of them came to is
 * offered for a case it says nothing about.
 *
 * <p><b>A proof only where every alternative there was proved it.</b> The rules leaving one
 * alternative nothing say nothing about the one beside it, and an alternative never tried — past a
 * figure, or under a case whose reading stopped — may have what the others lacked.
 *
 * <p><b>What the alternatives found out is every one's, joined whole</b> ({@link SearchShortfall}):
 * every figure and population met, every offer short of a rule, and a candidate turned away by any
 * of them, together with what was never tried.
 *
 * <p><b>Nothing here turns on the order the alternatives were tried in.</b> The one whose word is
 * said is the first in the order a report says the words in ({@link PublicationOrders}), which is
 * how every other reader puts several of them in one order; and where what was found out is more
 * than it found out itself, the word is the one for all of it ({@link SearchShortfall#wordFor}).
 *
 * <p><b>Rows passed over are the caller's answer and carry what was found out.</b> One alternative
 * that composed is the answer and ends the walk. Where rows were composed and the caller passed
 * over every one, that is the answer — but not one that may lose what the other alternatives found
 * out: rows passed over under the ways tried say nothing about an offer another way was short of,
 * or a way the walk stopped before.
 */
final class WhatTheAlternativesCameTo {

    private WhatTheAlternativesCameTo() {}

    /**
     * How one vocabulary of what a search came to is read and written here.
     *
     * @param <F> what one alternative came to
     */
    interface Vocabulary<F> {

        /** Whether {@code one} is the rules leaving nothing, which this compiler did not cause. */
        boolean proves(F one);

        /** The word {@code one} came to. */
        Generator.UnresolvedCombination.Reason word(F one);

        /** What {@code one} found out beside its word. */
        SearchShortfall found(F one);

        /**
         * {@code said}, carrying {@code found} in place of what it found out itself — and in the
         * word for it, since it is more than {@code said} found out by itself.
         */
        F carrying(F said, SearchShortfall found);
    }

    /**
     * What a walk over alternatives none of which was taken came to.
     *
     * @param <F> what one alternative came to
     */
    sealed interface Came<F> {

        /**
         * Rows were composed and every one was passed over, which is the caller's answer and not
         * a failure.
         *
         * @param found what every alternative found out, and what kept the walk from trying the
         *              rest: a figure or an offer short of a rule here is a row the search may yet
         *              have, and is not lost behind rows somebody did not want
         */
        record PassedOver<F>(SearchShortfall found) implements Came<F> {}

        /** What the alternatives that came to nothing came to, said in one of them. */
        record Said<F>(F said) implements Came<F> {}

        /**
         * No alternative to say it in, and the walk found out something of this compiler's beside
         * them: it stopped short of the rest.
         *
         * @param found what it found out
         */
        record Untried<F>(SearchShortfall found) implements Came<F> {

            public Untried {
                if (found.nothing()) {
                    throw new IllegalArgumentException(
                            "a walk said to have stopped short says what stopped it");
                }
            }
        }

        /**
         * No alternative to say it in, and nothing of this compiler's to carry: none was tried, or
         * every one tried proved nothing composes and the rest stand under a case nobody read. What
         * is said then is the caller's, since only it knows the words for its walk.
         */
        record NothingToSayItIn<F>() implements Came<F> {}
    }

    /**
     * What a walk over alternatives none of which was taken came to.
     *
     * @param cameToNothing every alternative tried that came to nothing
     * @param passedOver    what the walks of the rows passed over found out, or null where none
     *                      was: rows passed over are the answer
     * @param alsoFound     what the walk found out beside the alternatives that came to nothing:
     *                      what kept it from trying the rest, and, where they are not the answer,
     *                      what the walks of rows it passed over found out. Anything here is
     *                      something between the alternatives tried and all of them, so no proof
     *                      is said beside it
     * @param someUnread    whether an alternative stands under a case the row can be whose reading
     *                      stopped
     */
    static <F> Came<F> over(List<F> cameToNothing, SearchShortfall passedOver,
                            SearchShortfall alsoFound, boolean someUnread,
                            Vocabulary<F> how) {
        SearchShortfall found = alsoFound;
        for (F each : cameToNothing) {
            found = found.and(how.found(each));
        }
        if (passedOver != null) {
            return new Came.PassedOver<>(passedOver.and(found));
        }
        Optional<F> said = said(cameToNothing, found, alsoFound, someUnread, how);
        if (said.isPresent()) {
            return new Came.Said<>(said.get());
        }
        return alsoFound.nothing() ? new Came.NothingToSayItIn<>()
                : new Came.Untried<>(alsoFound);
    }

    /**
     * What {@code cameToNothing} came to where no row was passed over, said in one of them — or
     * empty where none of them is it.
     */
    private static <F> Optional<F> said(List<F> cameToNothing, SearchShortfall found,
                                        SearchShortfall alsoFound, boolean someUnread,
                                        Vocabulary<F> how) {
        // The first in the order a report says them, and among one word by everything else it
        // says, as a report orders two of them.
        Comparator<F> asSaid = Comparator
                .comparingInt((F each) -> PublicationOrders.positionOf(how.word(each)))
                .thenComparing(String::valueOf);
        Optional<F> notAProof = cameToNothing.stream().filter(each -> !how.proves(each))
                .min(asSaid);
        if (notAProof.isEmpty()) {
            // Every one tried proved it, or none was tried. A proof is the answer only where they
            // were every one there was; otherwise what was not tried is said, where it is anything
            // of this compiler's.
            Optional<F> proof = cameToNothing.stream().min(asSaid);
            if (proof.isEmpty()) {
                return Optional.empty();
            }
            if (!alsoFound.nothing()) {
                return Optional.of(how.carrying(proof.get(), found));
            }
            return someUnread ? Optional.empty() : proof;
        }
        F said = notAProof.get();
        return found.equals(how.found(said)) ? notAProof : Optional.of(how.carrying(said, found));
    }
}
