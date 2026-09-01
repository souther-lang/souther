package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.CompositionBudget;

import java.util.Collections;
import java.util.EnumSet;
import java.util.LinkedHashSet;
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
 * <p>So this is the projection an account reads: whether there are grounds, whether a budget of
 * this compiler's stopped the establishing of any, or whether there is simply nothing. The middle
 * one is the whole of what {@link #of} adds, and it is narrow — a value was composed and the
 * reading that would have placed it did not come back. A search that ran and found nothing, a
 * search nobody could run, and a point nobody asked about are all the third case: none of them met
 * a budget on the way to an answer, and calling them prevented would say this compiler was stopped
 * where it was not.
 *
 * <p><b>Nothing here says a row can be written.</b> {@link Prevented} is the question left open and
 * never the answer yes — a reader that took it for one would be turning an observation this
 * compiler cut short into the model admitting a row, which is the mistake it exists to name, made
 * backwards.
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
     * Budgets of this compiler's stopped the establishing, and these are which.
     *
     * <p>A set, and one that holds at most one of each kind. Two readings of one point may have
     * been stopped by two different figures, and neither of them outranks the other — what a reader
     * wants is everything that would have to be raised, and a choice between them would tell them
     * about whichever reading a walk happened to reach first.
     *
     * <p>Normalised here rather than by whoever collects them. Two observations that each name a
     * cause are one observation naming both, and two composings are one composing naming every
     * budget: held unnormalised, the same two facts arriving in two orders would be two different
     * values, and a law about the order readings are folded in could not be stated as an equality.
     */
    record Prevented(Set<EstablishmentGap> by) implements WritabilityKnowledge {

        public Prevented {
            Objects.requireNonNull(by, "a showing that was stopped says what stopped it");
            by = normalised(by);
            if (by.isEmpty()) {
                throw new IllegalArgumentException(
                        "a showing that was stopped says what stopped it");
            }
        }

        /** One gap of each kind, holding between them everything the kinds were given. */
        private static Set<EstablishmentGap> normalised(Set<EstablishmentGap> gaps) {
            Set<Incompleteness.Code> observed = EnumSet.noneOf(Incompleteness.Code.class);
            Set<CompositionBudget> budgets = EnumSet.noneOf(CompositionBudget.class);
            for (EstablishmentGap each : gaps) {
                switch (each) {
                    case EstablishmentGap.Observation it -> observed.addAll(it.causes());
                    case EstablishmentGap.Composition it -> budgets.addAll(it.budgets());
                }
            }
            Set<EstablishmentGap> out = new LinkedHashSet<>();
            if (!observed.isEmpty()) {
                out.add(new EstablishmentGap.Observation(observed));
            }
            if (!budgets.isEmpty()) {
                out.add(new EstablishmentGap.Composition(budgets));
            }
            return Collections.unmodifiableSet(out);
        }

        /** One gap that was made, for a caller that has exactly one. */
        public static Prevented by(EstablishmentGap gap) {
            return new Prevented(Set.of(gap));
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
     */
    static WritabilityKnowledge of(ItemAssessment.WritabilityEvidence evidence,
                                   java.util.List<ItemAssessment.Attempt> attempts) {
        if (evidence.known()) {
            return new Established(evidence);
        }
        // Asked of the outcome's own case and never of the reason inside it: a search that came
        // back with nothing has already lost which budget it was, so a reader rebuilding that from
        // the word left over is rebuilding what the word does not hold.
        //
        // Exhaustive, so that an outcome added is classified here rather than falling to the last
        // arm. Which of the five this is decides nothing on its own — what decides is whether it is
        // one a budget of this compiler's stopped, and that is a question the outcomes answer by
        // implementing {@link ItemAssessment.Attempt.Prevented} or not.
        //
        // Over every search of the point and not one of them. A point is searched once per reading
        // of its line, two readings can have been stopped by two different figures, and what a
        // reader is owed is everything that would have to give — so the gaps are collected and
        // never ranked.
        Set<EstablishmentGap> stopped = new LinkedHashSet<>();
        for (ItemAssessment.Attempt each : attempts) {
            if (each == null) {
                continue;   // nobody asked for a value to be built under that reading
            }
            switch (each) {
                case ItemAssessment.Attempt.Prevented it -> stopped.add(it.by());
                case ItemAssessment.Attempt.Certified _, ItemAssessment.Attempt.Unresolved _,
                     ItemAssessment.Attempt.Unavailable _ -> { }
            }
        }
        return stopped.isEmpty() ? new NoEvidence() : new Prevented(stopped);
    }
}
