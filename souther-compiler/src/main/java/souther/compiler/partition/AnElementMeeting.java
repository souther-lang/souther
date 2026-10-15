package souther.compiler.partition;

import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * What an element of a container meeting what is counted asks, as the reading of a condition that
 * some element meets it comes to ({@link DemandReading#anElementMeeting}): read once, and both of
 * what it says kept.
 *
 * @param heldTo   what the element is held to, as relations a region is narrowed by, where it is
 *                 that and nothing else
 * @param handedOn what another container is asked about the element, where it is one such demand
 *                 and nothing else: some entry of it keyed by the element, or some element of it
 *                 the element's value — which the element meets by what that container is made to
 *                 hold ({@link ACountHandedOn})
 */
record AnElementMeeting(Optional<List<TakenConstraint>> heldTo,
                        Optional<RowDemand.WithinIt> handedOn) {

    /** Nothing read of it. */
    static final AnElementMeeting UNREAD = new AnElementMeeting(Optional.empty(), Optional.empty());

    AnElementMeeting {
        Objects.requireNonNull(heldTo, "what an element is held to is said, or said to be unread");
        Objects.requireNonNull(handedOn, "what it hands on is said, or said to be nothing");
        heldTo = heldTo.map(List::copyOf);
    }
}
