package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.WhyNotTaken;

import java.time.Duration;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

/**
 * A condition of several ways whose every alternative holds the one before it is one object held
 * in two places, and the ways down a chain of them are two to its length. What the way states is
 * each condition once, in the order it is first met.
 */
class ConditionsHeldInSeveralPlacesOnAWayAreGoneDownOnceTest {

    private static final int LENGTH = 40;

    private static ConditionOccurrence condition(int which) {
        return new ConditionOccurrence("f", ConditionOccurrence.Reading.DECIDING, which);
    }

    private static ConditionReportAnchor anchor(int which) {
        return new ConditionReportAnchor.WhereTheReadingMetIt("example.ruled", condition(which));
    }

    private static OnTheWay.Declined declined(int which) {
        return new OnTheWay.Declined(condition(which), anchor(which),
                new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));
    }

    /** Each condition holds the one before it in both alternatives, and its own in one. */
    private static OnTheWay chainOf(int length) {
        OnTheWay held = declined(0);
        for (int at = 1; at <= length; at++) {
            held = OnTheWay.OneOf.of(condition(at), anchor(at),
                    List.of(List.of(held), List.of(held, declined(at))), Optional.empty());
        }
        return held;
    }

    @Test
    void aWayStatesEachConditionOfAChainOnceHoweverManyWaysLeadToIt() {
        WayToTheBorder way = new WayToTheBorder(List.of(chainOf(LENGTH)));

        List<OnTheWay> stated = assertTimeoutPreemptively(Duration.ofSeconds(10), way::stated);

        // The chain's conditions, and the one each adds beside the one before it, and the first.
        assertEquals(2 * LENGTH + 1, stated.size());
        assertEquals(stated.size(), stated.stream().distinct().count(), "each once");
    }
}
