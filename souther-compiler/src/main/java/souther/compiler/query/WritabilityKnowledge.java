package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.Collection;
import java.util.EnumSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/**
 * What this compilation knows about a row being writable at one point, and where the knowing
 * stopped.
 *
 * <p>Beside {@link ItemAssessment.WritabilityEvidence} and not instead of it. That collects the
 * grounds and holds nothing else, which is what makes an empty set the absence of evidence rather
 * than evidence of absence — and leaves the reader of the empty set with one answer for two
 * situations. Nothing has been shown, and nothing was tried, are alike only in what they lack.
 *
 * <p>So this is the projection an account reads, and it answers two questions at once. What the
 * model says — a row can be written here ({@link Established}), or no row can ({@link Refuted}) —
 * and, where the model has said neither, how far this compiler got: a budget of its own stopped the
 * establishing ({@link Prevented}), or there is simply nothing ({@link NoEvidence}). A search that
 * ran and found nothing, a search nobody could run, and a point nobody asked about are all the
 * last: none of them met a budget on the way to an answer, and calling them prevented would say
 * this compiler was stopped where it was not.
 *
 * <p><b>The two model answers are the two halves of one question and neither is a shade of the
 * epistemic pair.</b> The states were three, and what they sorted was how much this compiler had
 * managed — so a proof that the rules leave no value at the point came in as the residue, which is
 * the word for a point nothing was shown about. The question "can a row be written here" then had
 * a yes, two kinds of open, and no way to say no; and the no was read downstream as the second kind
 * of open, where it was counted as a question nobody could answer.
 *
 * <p><b>{@link Prevented} is not the answer no.</b> It is the question left open — a reader that
 * took it for one would be turning an observation this compiler cut short into the model refusing a
 * row, which is the mistake this exists to name. What says no is a proof about the model and
 * arrives only as one.
 */
public sealed interface WritabilityKnowledge {

    /**
     * Something has shown a row can be written here, and this is what.
     *
     * <p>Never nothing. An empty set of grounds is what {@link NoEvidence} is, and holding one here
     * would put the two states one field apart — a point with nothing behind it wearing the word
     * for a point with something, which is what an account reads to tell a finding from a gap.
     */
    record Established(ItemAssessment.WritabilityEvidence evidence)
            implements WritabilityKnowledge {

        public Established {
            if (evidence == null || !evidence.known()) {
                throw new IllegalArgumentException(
                        "a point something has shown writable says what showed it");
            }
        }
    }

    /**
     * The rules leave no value at the point, and every search made of it says so.
     *
     * <p>The one state here that is the model's own no, and it is the other half of
     * {@link Established} rather than a third kind of open. A point that reaches this is one no row
     * can be written at whatever anybody builds afterwards, so nothing a later search comes to
     * takes it back and nothing a reader raises reaches it.
     *
     * <p>Holds no word of its own. What proved it is the searches' to say and they still hold it,
     * a sentence per reading; a copy kept here would be the same fact written twice, free to differ
     * from the one a reader is shown under the point.
     *
     * <p>Established over the whole of what was searched ({@link SearchOutcomes#provesInfeasible()})
     * and never over one search of it. A proof is about the region the search that made it was
     * composed in, and a point is searched once per way of standing the dependencies in.
     */
    record Refuted() implements WritabilityKnowledge {}

    /**
     * Budgets of this compiler's stopped the establishing, and these are which.
     *
     * <p>All of them, at most one of each kind. Two readings of one point may have been stopped by
     * two different figures, and neither of them outranks the other — what a reader wants is
     * everything that would have to be raised, and a choice between them would tell them about
     * whichever reading a walk happened to reach first.
     *
     * <p>Put together by {@link #of} rather than by whoever collects them, and put in order after
     * that. So two runs that were stopped by the same things hold one value, whatever
     * order the readings arrived in and whatever order the kinds are declared in.
     */
    record Prevented(CanonicalSelection<EstablishmentGap> by) implements WritabilityKnowledge {

        public Prevented {
            Objects.requireNonNull(by, "a showing that was stopped says what stopped it");
            if (by.isEmpty()) {
                throw new IllegalArgumentException(
                        "a showing that was stopped says what stopped it");
            }
        }

        /**
         * Everything that stopped the showing, as one gap of each kind in the order they are
         * published in.
         *
         * <p>The two happen in that order and not the other. What the kinds hold between them is
         * settled first, because two observations that each name a cause are one observation naming
         * both — held apart, the same two facts arriving in two orders would be two different
         * values, and a law about the order readings are folded in could not be stated as an
         * equality. Only what is left after that has an order, and it is the one order there is.
         */
        public static Prevented of(Collection<EstablishmentGap> gaps) {
            Set<Incompleteness.Code> observed = EnumSet.noneOf(Incompleteness.Code.class);
            Set<CompositionBudget> budgets = EnumSet.noneOf(CompositionBudget.class);
            // Beside the figures and not among them. Two composings that came to nothing for two
            // kinds of reason are one composing gap, which is what a reader of a gap is told; what
            // each of them would take to close stays its own, and a fold that put them in one set
            // would have to lose one of the two.
            Set<CompositionRepertoire> repertoires = EnumSet.noneOf(CompositionRepertoire.class);
            for (EstablishmentGap each : gaps) {
                switch (each) {
                    case EstablishmentGap.Observation it -> observed.addAll(it.causes().written());
                    case EstablishmentGap.Composition it -> {
                        budgets.addAll(it.budgets().written());
                        repertoires.addAll(it.repertoires().written());
                    }
                }
            }
            List<EstablishmentGap> kinds = new ArrayList<>();
            if (!observed.isEmpty()) {
                kinds.add(EstablishmentGap.Observation.of(observed));
            }
            if (!budgets.isEmpty() || !repertoires.isEmpty()) {
                kinds.add(EstablishmentGap.Composition.of(budgets, repertoires));
            }
            return new Prevented(PublicationOrders.ESTABLISHMENT_GAPS.keep(kinds));
        }

        /** One gap that was made, for a caller that has exactly one. */
        public static Prevented by(EstablishmentGap gap) {
            return of(List.of(gap));
        }
    }

    /** Nothing has shown a row can be written here, and nothing was stopped from showing it. */
    record NoEvidence() implements WritabilityKnowledge {}

    /**
     * Where the grounds and the attempt beside them put the point.
     *
     * <p>Derived here and held nowhere, for the reason the evidence is: both are answers to
     * questions the assessment already carries, and a copy kept beside them is a state somebody can
     * build in which they disagree.
     *
     * <p>Grounds first. A point something has shown writable is established whatever a later search
     * made of it — a value built and not read back does not take back what the rules already prove,
     * and the order says so rather than leaving it to whichever the caller looked at.
     *
     * <p>Then the model's other answer, and only then how far this compiler got. What the searches
     * prove about the model settles the point, so a figure one of them met on the way is not what a
     * reader is told about it — and a point where one search proved and another was stopped is not
     * proved at all, which is the quantifier's answer and not this order's.
     */
    static WritabilityKnowledge of(ItemAssessment.WritabilityEvidence evidence,
                                   SearchOutcomes searches) {
        if (evidence.known()) {
            return new Established(evidence);
        }
        if (searches.provesInfeasible()) {
            return new Refuted();
        }
        // Asked of the outcome's own case and never of the reason inside it: a search that came
        // back with nothing has already lost what it fell short by, so a reader rebuilding that
        // from the word left over is rebuilding what the word does not hold.
        //
        // Exhaustive, so that an outcome added is classified here rather than falling to the last
        // arm. Which of them this is decides nothing on its own — what decides is whether it is one
        // this compiler fell short on, by a figure or by writing some of a population, and that is
        // a question the outcomes answer by implementing {@link ItemAssessment.Attempt.Prevented}
        // or not.
        //
        // Over every search of the point and not one of them. A point is searched once per reading
        // of its line, two readings can have been stopped by two different figures, and what a
        // reader is owed is everything that would have to give — so the gaps are collected and
        // never ranked.
        Set<EstablishmentGap> stopped = searches.prevented();
        return stopped.isEmpty() ? new NoEvidence() : Prevented.of(stopped);
    }
}
