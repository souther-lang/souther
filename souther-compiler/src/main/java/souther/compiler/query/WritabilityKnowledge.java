package souther.compiler.query;

import java.util.Objects;

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

    /** A budget of this compiler's stopped the establishing, and this is which. */
    record Prevented(EstablishmentGap by) implements WritabilityKnowledge {

        public Prevented {
            Objects.requireNonNull(by, "a showing that was stopped says what stopped it");
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
                                   ItemAssessment.Attempt attempt) {
        if (evidence.known()) {
            return new Established(evidence);
        }
        // The one thing that was stopped rather than absent. Read off the attempt's own case and
        // never off the reason inside an unresolved one: a search that came back with nothing has
        // already lost which budget it was, so a reader rebuilding that from the word left over is
        // rebuilding what the word does not hold.
        if (attempt instanceof ItemAssessment.Attempt.Unverified it) {
            return new Prevented(it.why());
        }
        return new NoEvidence();
    }
}
