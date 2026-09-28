package souther.compiler.values;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading carries one work order however it was assembled.
 *
 * <p>{@code APlannedReadingAnswersTheSameInEitherIterationOrderTest} already holds the walk to
 * answering the same either way, and says in so many words that what is asked of it is not how much
 * it read. Its questions are pure: nothing one block asks can change what another is told. The walk
 * this compiler actually runs is not — {@code Confinement.admission} builds one meter and hands it
 * to every question asked under it, so a question answered early leaves less for the ones after it,
 * and a question with nothing left comes back undecided rather than waiting.
 *
 * <p>So this holds the one thing neither of those covers. The meet is commutative and the walk
 * stops only where nothing further could move it, so the algebra is right; what carries the order
 * into the answer is beside the algebra, and is that the questions share what they are allowed to
 * spend. Reached late, the alternative that admits is asked with nothing left and comes back
 * undecided — and a reading written the other way round is the same reading.
 *
 * <p><b>Held of the reading and not of one walk over it.</b> The order the work is done in is a
 * function of what the reading is, settled where the reading is put together, so a walk cannot be
 * written that does not have it — which is what the first case here holds, and is why the walks
 * over a reading are not watched one at a time. They were, and the walk nobody thought to watch
 * was the one that went on reading the writing.
 *
 * <p><b>What is spent is held too, and not only what is answered.</b> The same contract
 * {@code HowAlternativesRelateTwoPositionsIsPartOfWhatAReadingCostsTest} takes over readings met
 * together: one semantic value is one schedule, so it costs what it costs however it was written.
 * Holding the answer alone would leave a walk free to reach it by spending a different amount on a
 * different order of questions, which is the same defect one step further in — the next question
 * asked under that allowance would then be the one that comes back undecided.
 */
class AReadingsAnswerDoesNotFollowWhichAlternativeSpentTheSharedAllowanceFirstTest {

    private static final Value A = Value.text("A");

    private static final Value B = Value.text("B");

    private static final Value C = Value.text("C");

    /** What one walk came to and what it spent getting there. */
    private record Walked(Emptiness answered, int spent) {}

    /** A rule about one position while it is still a description. */
    private static PlannedValues<String> plans(String atom, Value value) {
        return PlannedValues.at(atom, AdmittedPlan.of(ValueSet.just(value)));
    }

    /** An alternative naming two positions. */
    private static PlannedValues<String> alternative(Value here, Value there) {
        return plans("here", here).meet(plans("there", there));
    }

    /**
     * Walks {@code reading} with an allowance of {@code allowed}, answering that it could not tell
     * once there is nothing left — which is what a metered question does rather than spending what
     * it has not got.
     */
    private static Walked walked(PlannedValues<String> reading, int allowed) {
        int[] left = {allowed};
        Emptiness answered = reading.anyAlternativeAdmits((_, set) -> {
            if (left[0] <= 0) {
                return Emptiness.UNDECIDED;
            }
            left[0]--;
            return set.equals(ValueSet.just(C)) ? Emptiness.NONEMPTY : Emptiness.EMPTY;
        });
        return new Walked(answered, allowed - left[0]);
    }

    /** The alternatives a reading hands out, in the order it hands them out in. */
    private static java.util.List<String> handedOut(PlannedValues<String> reading) {
        PlannedHeld<String> held = ((PlannedValues.Settled<String>) reading).held();
        return ((PlannedHeld.Alternatives<String>) held).boxes().stream()
                .map(Object::toString).toList();
    }

    /** The same reading, written each way round. */
    private static PlannedValues<String> oneWay() {
        return alternative(A, B).joinLiveApart(alternative(C, C));
    }

    private static PlannedValues<String> theOther() {
        return alternative(C, C).joinLiveApart(alternative(A, B));
    }

    /**
     * The control: with more allowance than the walk can spend, neither the answer nor what it cost
     * turns on the writing. Without this the case below would say nothing — two orders agreeing
     * means nothing if they would agree whatever the walk did.
     */
    @Test
    void withAllowanceToSpareNeitherTheAnswerNorTheCostFollowsTheWriting() {
        Walked one = walked(oneWay(), 100);
        Walked other = walked(theOther(), 100);
        assertTrue(one.spent() > 0, "a walk that asked nothing would agree with anything");
        assertEquals(one, other,
                "nothing was short, so nothing turned on who asked first — and one reading is one"
                        + " schedule, so it costs what it costs however it was written down");
    }

    /**
     * And with an allowance one question short of what the walk would spend, neither does whether
     * the reading stands: the alternative that admits is asked while there is still something left,
     * wherever in the writing it happens to stand.
     */
    @Test
    void withTheAllowanceShortNeitherTheAnswerNorTheCostFollowsTheWriting() {
        Walked one = walked(oneWay(), 2);
        Walked other = walked(theOther(), 2);
        assertTrue(one.spent() > 0, "a walk that asked nothing would agree with anything");
        assertEquals(one, other,
                "the same reading, written the other way round: what the walk could tell, and what"
                        + " it spent telling it, are the reading's and not the writing's");
    }

    /**
     * The carrier hands out one order, and hands out the same one however it was put together.
     * Held of the reading itself, so that a walk written later cannot be the one that gets it
     * wrong — which is what the walks below would otherwise each have to be watched for.
     */
    @Test
    void oneReadingIsOneOrderHoweverItWasPutTogether() {
        assertEquals(handedOut(oneWay()), handedOut(theOther()),
                "the same reading, written the other way round: what it holds, and the order it"
                        + " hands them out in, are the reading's and not the writing's");
    }
}
