package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ReadersOfAGraph;
import souther.compiler.meaning.WhyNotTaken;
import souther.test.ClosedWorldContract;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reader of the conditions on a way asks each condition once, however many alternatives hold
 * it.
 *
 * <p>A condition of several ways holds the conditions of its alternatives, and a name used twice
 * puts one in two of them, so the conditions on a way are a graph and the ways down a chain of
 * them are two to its length ({@link ReadersOfAGraph}). Asked of a chain of conditions each holding
 * the one before it in both alternatives, as a way and as a condition.
 */
@ClosedWorldContract
class EveryReaderOfAWayAsksEachConditionOnceTest {

    /** Readers whose work is the ways down, which is what they are for. */
    private static final Map<String, String> BY_THEIR_NATURE = Map.of(
            "OnTheWay$OneOf.toString", "the text of the condition",
            "WayToTheBorder.toString", "the text of the conditions on the way");

    /** How many readers are asked at least, so that finding none is not a pass. */
    private static final int AT_LEAST_ASKED = 5;

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
    void noReaderOfTheConditionsOnAWayGoesDownEveryWayToThem() throws Exception {
        ReadersOfAGraph.Findings found = ReadersOfAGraph.askEach(List.of(
                new ReadersOfAGraph.Chain("conditions", OnTheWay.class,
                        EveryReaderOfAWayAsksEachConditionOnceTest::chainOf),
                new ReadersOfAGraph.Chain("a way of conditions", WayToTheBorder.class,
                        length -> new WayToTheBorder(List.of(chainOf(length))))),
                BY_THEIR_NATURE);

        assertEquals(Set.of(), found.slow());
        assertTrue(found.answered().size() >= AT_LEAST_ASKED, found.answered().size() + " readers asked");
    }
}
