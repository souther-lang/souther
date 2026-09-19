package souther.compiler.partition;

import souther.compiler.values.InOneOrder;

import java.util.Map;

/**
 * What became of each thing a run was asked for.
 *
 * <p>Keyed by the obligation itself, so what a reader joins a finding by is the identity the plan
 * used to ask. The entries used to carry that identity inside them as well and be held in a list,
 * which let one run hold an entry filed under one class whose value named another — and a reader
 * looking a class up by identity found whichever of the two the search wrote first.
 *
 * <p>Whether it covers the plan is {@link FillResult}'s to hold, since that is where the plan is.
 * This is the answers alone.
 *
 * <p>Held in no order at all. What a row is offered for is taken in the plan's order and everything
 * else asks by key, so two runs that answered the same obligations in two orders are one discharge
 * — and an order kept here would be one a reader could start reading and a sentence could start
 * saying. What is written out is written in one order ({@link #toString}), which is what a message
 * about one run reading the same way twice wanted of it.
 */
public record Discharge(Map<ClassOfAPosition, ClassDisposition> classes,
                        Map<Generator.ArmOwed, ArmDisposition> arms,
                        Map<ObligationIdentity.OfAFallbackPairCell, ClassDisposition> pairs,
                        Map<ObligationIdentity.OfACombinationOfDecisions, ClassDisposition>
                                meetings) {

    /** Nothing asked for and nothing answered, which is the only run this is right for. */
    public static final Discharge NOTHING =
            new Discharge(Map.of(), Map.of(), Map.of(), Map.of());

    public Discharge {
        // Neither half of an entry missing. A key with nothing under it is an obligation that was
        // asked about and not answered for, which is the absence every value here is arranged to
        // have none of — and it satisfied a check written over the keys alone.
        classes = Ordered.byKey(classes);
        arms = Ordered.byKey(arms);
        // A combination of two classes, under the same shape a class's answer has: a row was
        // composed for it or none was, and why. What differs between them is the requirement and
        // not the news about it.
        pairs = Ordered.byKey(pairs);
        // And a combination of the body's decisions, under that shape again. What a row is for
        // differs between the three; that a row was composed or none was does not.
        meetings = Ordered.byKey(meetings);
    }

    /** What became of each thing asked for, written in one order — see {@link InOneOrder}. */
    @Override
    public String toString() {
        return "classes " + InOneOrder.of(classes) + ", arms " + InOneOrder.of(arms)
                + ", pairs " + InOneOrder.of(pairs) + ", meetings " + InOneOrder.of(meetings);
    }

    /** What became of one combination of the body's decisions, or null where nothing asked. */
    public ClassDisposition at(ObligationIdentity.OfACombinationOfDecisions owed) {
        return meetings.get(owed);
    }

    /** What became of one combination of two classes, or null where nothing asked about it. */
    public ClassDisposition at(ObligationIdentity.OfAFallbackPairCell owed) {
        return pairs.get(owed);
    }

    /** What became of one class, or null where this run was not asked about it. */
    public ClassDisposition at(ClassOfAPosition owed) {
        return classes.get(owed);
    }

    /** What became of one arm, or null where this run was not asked about it. */
    public ArmDisposition at(Generator.ArmOwed owed) {
        return arms.get(owed);
    }

    /**
     * The same, asked at one of the places a run through the arm is recorded.
     *
     * <p>For a reader holding an occurrence rather than the arm — a finding names one site of the
     * arm it is about, and what the search was asked for is the arm and every splice of it. Asked
     * with the site's own probe as though it were the whole key, such a reader found nothing
     * whenever the arm stood in the body more than once.
     *
     * <p>Every entry read and not the first that matches. A probe is one place in one body, so at
     * most one arm is recorded at it — and answered with whichever entry came first, two writings
     * of one discharge would answer a reader two ways wherever that stopped being true. So the
     * answer is the one arm claiming the place, and several claiming it is refused.
     *
     * <p>Counted rather than gathered. What the refusal has to say is that a place is held twice,
     * and which arms those are is read off the discharge by whoever is looking — gathered here they
     * would be named in the order the entries happen to be held, which is the order this says
     * nothing is answered from.
     */
    public ArmDisposition at(souther.compiler.coverage.ArmProbe probe) {
        ArmDisposition only = null;
        int claiming = 0;
        for (Map.Entry<Generator.ArmOwed, ArmDisposition> each : arms.entrySet()) {
            if (each.getKey().recordedAt(probe)) {
                claiming++;
                only = each.getValue();
            }
        }
        if (claiming > 1) {
            throw new IllegalStateException("a place is recorded against more than one arm: "
                    + probe + " is held by " + claiming + " of them");
        }
        return only;
    }
}
