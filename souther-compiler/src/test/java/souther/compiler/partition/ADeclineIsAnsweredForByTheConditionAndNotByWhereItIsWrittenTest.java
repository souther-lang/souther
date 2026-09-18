package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.sites.WrittenCondition;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A decline the answer side answered for is the one it named, and not whichever decline a report
 * sends a reader to the same place for.
 *
 * <p>The account of a composing suppresses an input-side decline where the demand reading took the
 * condition up, since the reading over the input declines every condition about an answer whatever
 * became of it. What joins the two projections has to be the condition, and where a report about a
 * condition points is not one: a helper is spliced into each call of it, so one written condition
 * stands as many times as it is called and every one of those is reported at the one place it is
 * written — which
 * {@link AConditionOnTheWayIsNamedHereAndPlacedByWhoeverWroteItTest#twoConditionsReportedAtOnePlaceAreStillTwo()}
 * holds of the walk's own account.
 *
 * <p>Joined on the place, what became of one expansion would answer for the other: a condition the
 * answer side states in one call would take the decline of another call out of the account, and a
 * row composed without that one would be reported as composed against the whole of the way.
 */
class ADeclineIsAnsweredForByTheConditionAndNotByWhereItIsWrittenTest {

    /** Two conditions of one body, written in one place and told apart by the reading's name. */
    private static final ConditionOccurrence ONE = new ConditionOccurrence("decides", 0);
    private static final ConditionOccurrence THE_OTHER = new ConditionOccurrence("decides", 1);

    @Test
    void theDeclineTheAnswerSideDidNotNameIsStillInTheAccount() {
        WayToTheBorder way = new WayToTheBorder(List.of(declined(ONE), declined(THE_OTHER)));
        CompositionAccount account =
                new CompositionAccount(List.of(), List.of(), Set.of(ONE));

        assertEquals(List.of(new ConditionGap.OfTheInput(
                        new ReachabilityGap.Unstated(declined(THE_OTHER)))),
                account.reconciledWith(way),
                "the one the answer side named is answered for there, and the other is not");
    }

    /** And the two are one place, which is what makes the answer above worth reading. */
    @Test
    void andBothAreReportedAtOnePlace() {
        assertEquals(1, new LinkedHashSet<>(
                        List.of(declined(ONE).anchor(), declined(THE_OTHER).anchor())).size(),
                "a report about either sends a reader to where the condition is written");
        assertEquals(2, new LinkedHashSet<>(
                        List.of(declined(ONE).condition(), declined(THE_OTHER).condition())).size(),
                "and the reading's own name is what tells them apart");
    }

    /** A condition the walk had no words for, written where the one written condition is. */
    private static OnTheWay.Declined declined(ConditionOccurrence condition) {
        return new OnTheWay.Declined(condition, where(), new OnTheWay.Why.NoWordsForTheShape());
    }

    /** Where the one condition both of these came from is written. */
    private static ConditionReportAnchor where() {
        return new ConditionReportAnchor.WhereItIsWritten(
                new WrittenCondition.Construct(new SourceConstructOrigin(
                        new WrittenOwner.Body("example.helper", "either"), 0, 0,
                        SourceConstruct.BINARY)));
    }
}
