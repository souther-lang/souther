package souther.bench;

import org.junit.jupiter.api.Test;

import souther.bench.SaltedOrder.Reading;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Nothing in this compiler takes the iteration of a copy the partition makes into an answer before
 * the order is named.
 *
 * <p>What a copy through {@code Set.copyOf} or {@code Map.copyOf} hands back iterates in an order
 * the run decides. Holding one is not the defect, and neither is walking one: the readers of these
 * put them in an order the model publishes, fold them with an operation that does not care which
 * comes first, or ask only what they hold. What is refused is the walk that ends as a list of what
 * was met, the first one that matched, or a text that says them, with nothing between the copy and
 * the answer that puts them in an order.
 *
 * <p><b>Read from the copies and not from a list of what holds one.</b> Every call of the
 * partition's classes that makes an unordered value is where the reading begins, so a carrier added
 * tomorrow is read tomorrow, and one that goes back to a copy after being taken off one is read
 * again. What a value is followed through is the code: through what is kept in a field, handed to
 * a method, returned from one, or given to a function that walks it. It is not followed into a field
 * of another package, which is where {@link #WHERE_ITS_VALUES_LEAVE} says what leaves.
 *
 * <p>Beside two others that guard the far end of the same thing, and neither is asked here.
 * Nothing that reaches a report is an unordered plurality, and a field of a document whose order is
 * this compiler's is written from a sequence somebody put in order. What is asked here is what
 * comes before them: that a reader of the copies is not the one that decides an order.
 */
class AnOrderlessPartitionCarrierIsNotWalkedBeforeItsOrderIsNamedTest {

    private static final Predicate<String> COPIES_THE_PARTITION_MAKES =
            name -> name.startsWith("souther/compiler/partition/");

    /**
     * Where a value the partition copied is handed to a field of a class outside it.
     *
     * <p>The reading follows a value through the partition and out of it by what is returned, and
     * stops where one is stored in another package's class, because which object that is a field of
     * is not followed. What stops there is stated: a field added to this is a value that left
     * without anybody having said where it went. The first two are the numbers of a condition and
     * of a rule a report is written from, and are read where the report is made. The other holds
     * the direction of a quantity as the coefficients of a form, and is read where forms are.
     */
    private static final Set<String> WHERE_ITS_VALUES_LEAVE = Set.of(
            "souther.compiler.query.Coverages$Partitioned.conditionsMet",
            "souther.compiler.query.Coverages$Partitioned.rulesReachedAt",
            "souther.compiler.numeric.LinearForm.coefs");

    private static final String HANDED_ON = "handed on to a field outside what is read: ";

    private static Reading read;

    private static Reading thePartition() {
        if (read == null) {
            read = SaltedOrderFlow.read(Reactor.classes(), COPIES_THE_PARTITION_MAKES);
        }
        return read;
    }

    @Test
    void noReaderOfACopyTheClassesOfThePartitionMakeTakesItsIterationIntoAnAnswer() {
        Reading reading = thePartition();

        assertFalse(reading.roots().isEmpty(),
                "the partition makes no copy, so a rule read from its copies holds nothing");
        assertEquals(List.of(), reading.described(),
                "a reader takes the iteration of an unordered copy into an answer before an order"
                        + " is named — put the copy in an order the model publishes, or fold it with"
                        + " an operation that does not care which comes first");
    }

    /**
     * And every copy is followed to somewhere it can be said to end.
     *
     * <p>A copy that ended nowhere is one the walk lost, and a lost copy passes every rule about
     * where it goes. The count is not what is asserted, and it is not held: what is, is that no
     * copy the partition makes is one this could not place.
     */
    @Test
    void everyCopyIsFollowedToWhereItEnds() {
        Map<String, Set<String>> ends = thePartition().reachedInOrder();
        List<String> lost = new ArrayList<>();
        for (String copy : thePartition().roots()) {
            if (ends.getOrDefault(copy, Set.of()).isEmpty()) {
                lost.add(copy);
            }
        }

        assertEquals(List.of(), lost,
                "a copy the partition makes ended nowhere this could say, so what is done with it"
                        + " was not read");
    }

    @Test
    void whereTheValuesOfThePartitionLeaveItIsWhatIsSaid() {
        Set<String> left = new LinkedHashSet<>();
        for (Set<String> each : thePartition().reachedInOrder().values()) {
            for (String how : each) {
                if (how.startsWith(HANDED_ON)) {
                    left.add(how.substring(HANDED_ON.length()));
                }
            }
        }

        assertEquals(WHERE_ITS_VALUES_LEAVE, left,
                "a value the partition copied is handed to a field outside it that is not in the"
                        + " list, or a field in the list is not handed one. What a field holds is"
                        + " read by whoever reads it — so either widen what is read to the package"
                        + " it is in, or say where it is read");
    }
}
