package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walk of a form is worked out once for each order it is asked under, and is the walk the form
 * itself gives.
 *
 * <p>What a walk is settled by is the form and the order, so an order that keeps what it has been
 * asked answers the next asking from what it kept. Held here: that what comes back is
 * {@link CanonicalForm#entriesIn} in the same entries in the same order, that an order is not mixed
 * up with another, that a walk which is refused is refused each time, and that the order is put to
 * its comparisons once for a form however many times the form is asked.
 */
class AFormsWalkIsKeptForTheOrderItWasAskedUnderTest {

    private static CanonicalForm<String> form(String... positionsAndWeights) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        for (int at = 0; at < positionsAndWeights.length; at += 2) {
            coefs.put(positionsAndWeights[at], ExactRatio.of(Long.parseLong(
                    positionsAndWeights[at + 1])));
        }
        return new CanonicalForm<>(coefs);
    }

    private static CanonicalOrder<String> counting(AtomicInteger comparisons) {
        return (one, other) -> {
            comparisons.incrementAndGet();
            return one.compareTo(other);
        };
    }

    @Test
    void aFormAskedAgainIsWalkedFromWhatWasKept() {
        AtomicInteger comparisons = new AtomicInteger();
        CanonicalOrder<String> order = ClosedStates.kept().kept(counting(comparisons));
        CanonicalForm<String> form = form("c", "3", "a", "1", "d", "-2", "b", "5");

        List<Map.Entry<String, ExactRatio>> first = form.entriesIn(order);
        int afterTheFirst = comparisons.get();
        List<Map.Entry<String, ExactRatio>> second = form.entriesIn(order);

        assertTrue(afterTheFirst > 0, "the first asking walked the form");
        assertEquals(afterTheFirst, comparisons.get(), "the second asking put the order to its"
                + " comparisons again");
        assertEquals(first, second);
    }

    @Test
    void anEqualFormWrittenApartIsTheSameWalk() {
        AtomicInteger comparisons = new AtomicInteger();
        CanonicalOrder<String> order = ClosedStates.kept().kept(counting(comparisons));

        List<Map.Entry<String, ExactRatio>> first =
                form("c", "3", "a", "1", "b", "5").entriesIn(order);
        int afterTheFirst = comparisons.get();
        List<Map.Entry<String, ExactRatio>> second =
                form("b", "5", "c", "3", "a", "1").entriesIn(order);

        assertEquals(afterTheFirst, comparisons.get());
        assertEquals(first, second);
    }

    @Test
    void whatIsKeptIsTheWalkTheFormGives() {
        Random dice = new Random(2680);
        List<String> positions = List.of("a", "b", "cc", "x", "y", "zz", "m", "n");
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        CanonicalOrder<String> kept = ClosedStates.kept().kept(order);
        for (int round = 0; round < 300; round++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            int howMany = 1 + dice.nextInt(positions.size());
            for (int at = 0; at < howMany; at++) {
                coefs.put(positions.get(dice.nextInt(positions.size())),
                        ExactRatio.of((dice.nextBoolean() ? 1L : -1L) * (1 + dice.nextInt(7))));
            }
            CanonicalForm<String> form = new CanonicalForm<>(coefs);

            assertEquals(form.entriesIn(order), form.entriesIn(kept), "asked first");
            assertEquals(form.entriesIn(order), form.entriesIn(kept), "asked again");
        }
    }

    /** The same form under another order is another walk: what was kept for one is not handed to
     *  the other. */
    @Test
    void anotherOrderIsAnotherWalk() {
        ClosedStates table = ClosedStates.kept();
        CanonicalOrder<String> forwards = table.kept(CanonicalOrder.asTheyAreSpelled());
        CanonicalOrder<String> backwards = table.kept((one, other) -> other.compareTo(one));
        CanonicalForm<String> form = form("c", "3", "a", "1", "b", "5");

        List<Map.Entry<String, ExactRatio>> up = form.entriesIn(forwards);
        List<Map.Entry<String, ExactRatio>> down = form.entriesIn(backwards);

        assertEquals(List.of("a", "b", "c"), up.stream().map(Map.Entry::getKey).toList());
        assertEquals(List.of("c", "b", "a"), down.stream().map(Map.Entry::getKey).toList());
        assertEquals(up, form.entriesIn(forwards));
        assertEquals(down, form.entriesIn(backwards));
    }

    /** Two positions an order cannot tell apart are refused as they are by the form, each time. */
    @Test
    void aWalkThatIsRefusedIsRefusedEachTimeItIsAsked() {
        CanonicalOrder<String> byLength = ClosedStates.kept().kept(
                (one, other) -> Integer.compare(one.length(), other.length()));
        CanonicalForm<String> tied = form("a", "1", "b", "1");

        assertThrows(IllegalStateException.class, () -> tied.entriesIn(byLength));
        assertThrows(IllegalStateException.class, () -> tied.entriesIn(byLength));
    }

    @Test
    void aTableThatKeepsNothingWalksTheFormEachTime() {
        AtomicInteger comparisons = new AtomicInteger();
        CanonicalOrder<String> asked = counting(comparisons);
        CanonicalOrder<String> order = ClosedStates.NONE.kept(asked);
        CanonicalForm<String> form = form("c", "3", "a", "1", "b", "5");

        assertSame(asked, order, "a table that keeps nothing hands the order back");
        List<Map.Entry<String, ExactRatio>> first = form.entriesIn(order);
        int afterTheFirst = comparisons.get();
        List<Map.Entry<String, ExactRatio>> second = form.entriesIn(order);

        assertEquals(2 * afterTheFirst, comparisons.get());
        assertEquals(first, second);
    }

    /** An order already kept is not kept again, and one order is one entry however often asked. */
    @Test
    void anOrderIsKeptOnce() {
        ClosedStates table = ClosedStates.kept();
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();

        assertSame(table.kept(order), table.kept(order));
        assertSame(table.kept(order), table.kept(table.kept(order)));
    }

    /**
     * Two domains made apart over the same rules, through one table: the second is asked about the
     * forms of the rules the first was, and walks none of them again.
     */
    @Test
    void aDomainMadeApartOverTheSameRulesWalksTheRulesFormsOnce() {
        ClosedStates table = ClosedStates.kept();
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        NumberSpace counted = NumberSpace.spacedOnly(Granularity.DISCRETE);
        Map<String, NumberSpace> spacing = Map.of("a", counted, "b", counted, "c", counted,
                "d", counted);
        LinearForm<String> sum = new LinearForm<>(ExactRatio.of(-30), orderedCoefs());
        LinearForm<String> question = new LinearForm<>(ExactRatio.ZERO, orderedCoefs());

        long walksAfter = 0;
        for (int domain = 0; domain < 3; domain++) {
            NumericDomain<String> made = NumericDomain.top(order, table)
                    .assume(sum, Rel.LE, spacing)
                    .assume(LinearForm.atomMinusConstant("a", ExactRatio.of(3)), Rel.GE, spacing)
                    .assume(LinearForm.atomMinusConstant("b", ExactRatio.of(2)), Rel.GE, spacing);
            made.boundsOf(question);
            if (domain == 0) {
                walksAfter = table.walksWorkedOut();
                assertTrue(walksAfter > 0, "the first domain walked the rules' forms");
            }
        }

        assertEquals(walksAfter, table.walksWorkedOut(),
                "a domain made apart over the same rules walked their forms again");
    }

    private static Map<String, ExactRatio> orderedCoefs() {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put("d", ExactRatio.of(1));
        coefs.put("c", ExactRatio.of(2));
        coefs.put("b", ExactRatio.of(1));
        coefs.put("a", ExactRatio.of(3));
        return coefs;
    }
}
