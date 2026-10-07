package souther.compiler.partition;

import souther.compiler.inputs.TermPath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Optional;
import java.util.SequencedMap;

/**
 * What several alternatives for one choice came to, where none of them composed — said once, over
 * every one of them.
 *
 * <p>The ways of writing a row under the cases of a sum, the ways a stated value is written, the
 * values of a parameter a later one turns on: each is a walk over alternatives, and what it comes
 * to when none composes is one answer about all of them. Kept as the answer of one of them, the
 * rest are dropped — a figure one of them stopped at is a number nobody is told to raise, and a
 * proof one of them came to is offered for a case it says nothing about.
 *
 * <p><b>A proof only where every alternative there was proved it.</b> The rules leaving one
 * alternative nothing say nothing about the one beside it, and an alternative never tried — past a
 * figure, or under a case whose reading stopped — may have what the others lacked.
 *
 * <p><b>What this compiler fell short by is every alternative's, joined.</b> Whichever was tried
 * first, a reader is owed every figure, population and offer any of them met, together with what
 * was never tried. The word is the first alternative's that proved nothing, and becomes the word
 * for what was met wherever another alternative met more than it did — so whether the answer is a
 * proof, and everything it carries, does not turn on the order they were tried in.
 *
 * <p><b>Rows passed over are the caller's answer and carry what was met.</b> One alternative that
 * composed is the answer and ends the walk. Where rows were composed and the caller passed over
 * every one, that is the answer — but not one that may lose a figure: rows passed over under the
 * ways tried say nothing about a way the walk stopped before.
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

        /** What of this compiler's {@code one} met. */
        CompositionShortfall met(F one);

        /** What the rules about the positions left out of what {@code one} was offered. */
        SequencedMap<TermPath, StringOfferShortfall> offered(F one);

        /**
         * {@code said}, carrying {@code met} and {@code offered} in place of its own — in the word
         * for them, since they are more than {@code said} met by itself.
         */
        F carrying(F said, CompositionShortfall met,
                   SequencedMap<TermPath, StringOfferShortfall> offered);
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
         * @param met what every alternative met, and what kept the walk from trying the rest: a
         *            figure here is a row raising it may yet offer, and is not lost behind rows
         *            somebody did not want
         */
        record PassedOver<F>(CompositionShortfall met) implements Came<F> {}

        /** What the alternatives that came to nothing came to, said in one of them. */
        record Said<F>(F said) implements Came<F> {}

        /**
         * No alternative to say it in, and the walk stopped short of the rest.
         *
         * @param met what stopped it
         */
        record Untried<F>(CompositionShortfall met) implements Came<F> {

            public Untried {
                if (met.nothing()) {
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
     * @param cameToNothing every alternative tried that came to nothing, in the order they were
     * @param passedOver    what the walks of the rows passed over met, or null where none was
     * @param alsoMet       what kept the walk from trying the rest. Anything here is something of
     *                      this compiler's between the alternatives tried and all of them, so no
     *                      proof is said beside it
     * @param someUnread    whether an alternative stands under a case the row can be whose reading
     *                      stopped
     */
    static <F> Came<F> over(List<F> cameToNothing, CompositionShortfall passedOver,
                            CompositionShortfall alsoMet, boolean someUnread,
                            Vocabulary<F> how) {
        if (passedOver != null) {
            CompositionShortfall met = passedOver.and(alsoMet);
            for (F each : cameToNothing) {
                met = met.and(how.met(each));
            }
            return new Came.PassedOver<>(met);
        }
        Optional<F> said = said(cameToNothing, alsoMet, someUnread, how);
        if (said.isPresent()) {
            return new Came.Said<>(said.get());
        }
        return alsoMet.nothing() ? new Came.NothingToSayItIn<>() : new Came.Untried<>(alsoMet);
    }

    /**
     * What {@code cameToNothing} came to where no row was passed over, said in one of them — or
     * empty where none of them is it.
     */
    private static <F> Optional<F> said(List<F> cameToNothing, CompositionShortfall alsoMet,
                                        boolean someUnread, Vocabulary<F> how) {
        if (cameToNothing.isEmpty()) {
            return Optional.empty();
        }
        CompositionShortfall met = alsoMet;
        SequencedMap<TermPath, StringOfferShortfall> offered = new LinkedHashMap<>();
        F said = null;
        for (F each : cameToNothing) {
            met = met.and(how.met(each));
            how.offered(each).forEach((at, gap) ->
                    offered.merge(at, gap, StringOfferShortfall::and));
            if (said == null && !how.proves(each)) {
                said = each;
            }
        }
        if (said == null) {
            // Every one tried proved it. That is the answer only where they were every one there
            // was; otherwise what was not tried is said, where it is anything of this compiler's.
            F first = cameToNothing.getFirst();
            if (!alsoMet.nothing()) {
                return Optional.of(how.carrying(first, met, offered));
            }
            return someUnread ? Optional.empty() : Optional.of(first);
        }
        return met.equals(how.met(said)) && offered.equals(how.offered(said)) ? Optional.of(said)
                : Optional.of(how.carrying(said, met, offered));
    }
}
