package souther.compiler.partition;

import org.junit.jupiter.api.Test;

/**
 * No way some group of the input meets is shown to be one no row takes, whatever quantifiers over
 * the items inside a group ask: what two of them ask is met by two items, which may differ.
 *
 * <p>Asked of the first shape of each structure ({@link WaysOfTheirOwnElements#ofEachStructure}),
 * which is what a change to how a way is read or a row is composed has to get right at once. Every
 * shape is asked in {@link AWayElementsOfTheirOwnMeetIsNeverShownClosedAtEveryShapeTest}.
 */
class AWayElementsOfTheirOwnMeetIsNeverShownClosedTest {

    private static final WaysOfTheirOwnElements WAYS =
            new WaysOfTheirOwnElements(WaysOfTheirOwnElements.ofEachStructure());

    @Test
    void noWaySomeGroupMeetsIsShownClosed() {
        WAYS.noWaySomeGroupMeetsIsShownClosed();
    }

    @Test
    void noRowComposedPastAWaySomeGroupMeetsIsShownImpossible() {
        WAYS.noRowComposedPastAWaySomeGroupMeetsIsShownImpossible();
    }

    @Test
    void aWayNoGroupMeetsWhereItIsAskedExactlyIsClosed() {
        WAYS.aWayNoGroupMeetsWhereItIsAskedExactlyIsClosed();
    }

    @Test
    void whatIsLeftOfAnElementDoesNotTurnOnTheOrderItIsAskedIn() {
        WAYS.whatIsLeftOfAnElementDoesNotTurnOnTheOrderItIsAskedIn();
    }

    @Test
    void aLineOnAnotherNumberPastAGuardSomeGroupMeetsIsTheLineItDrawsPastAnyOther() {
        WaysOfTheirOwnElements.aLineOnAnotherNumberPastAGuardSomeGroupMeetsIsTheLineItDrawsPastAnyOther();
    }

    @Test
    void theWaysEveryItemMeetingOneOfSeveralIsWrittenInAreHeldToTheFigure() {
        WaysOfTheirOwnElements.theWaysEveryItemMeetingOneOfSeveralIsWrittenInAreHeldToTheFigure();
    }
}
