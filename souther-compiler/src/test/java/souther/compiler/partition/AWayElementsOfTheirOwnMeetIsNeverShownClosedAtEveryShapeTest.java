package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.test.ClosedWorldContract;
import souther.test.Nightly;

/**
 * The claims of {@link AWayElementsOfTheirOwnMeetIsNeverShownClosedTest}, asked of every shape
 * ({@link WaysOfTheirOwnElements#everyShape}) and not of the first of each structure.
 *
 * <p>Why it is deferred. Composing a row past each of the shapes and compiling the behaviors they
 * are written as cost about twenty seconds, which grows with the shapes there are. No cheaper way
 * to ask every shape was found: the numbers in a shape change what is met and so which way a row
 * is composed by, and the structures do not tell which shapes of one differ.
 *
 * <p>Why the morning is soon enough. What it holds is that a way is not called closed, and a row
 * not called impossible, where some group meets it. A change that breaks that for a shape no
 * structure's first stands for is found the night after, among the day's merges, and the claim for
 * each structure is asked on every change in the class this is the full run of.
 */
@Nightly
@ClosedWorldContract
class AWayElementsOfTheirOwnMeetIsNeverShownClosedAtEveryShapeTest {

    private static final WaysOfTheirOwnElements WAYS =
            new WaysOfTheirOwnElements(WaysOfTheirOwnElements.everyShape());

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
}
