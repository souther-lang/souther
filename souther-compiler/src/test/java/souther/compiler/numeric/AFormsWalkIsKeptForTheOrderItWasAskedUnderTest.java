package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The walk of a form is worked out once for each order it is asked under, and is the walk the form
 * itself gives.
 *
 * <p>What a walk is settled by is the form and the order, so a table that keeps what it has been
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
        CanonicalOrder<String> order = counting(comparisons);
        Function<CanonicalForm<String>, List<Map.Entry<String, ExactRatio>>> walks =
                ClosedStates.kept().walksIn(order);
        CanonicalForm<String> form = form("c", "3", "a", "1", "d", "-2", "b", "5");

        List<Map.Entry<String, ExactRatio>> first = walks.apply(form);
        int afterTheFirst = comparisons.get();
        List<Map.Entry<String, ExactRatio>> second = walks.apply(form);

        assertTrue(afterTheFirst > 0, "the first asking walked the form");
        assertEquals(afterTheFirst, comparisons.get(), "the second asking put the order to its"
                + " comparisons again");
        assertEquals(first, second);
    }

    @Test
    void anEqualFormWrittenApartIsTheSameWalk() {
        AtomicInteger comparisons = new AtomicInteger();
        Function<CanonicalForm<String>, List<Map.Entry<String, ExactRatio>>> walks =
                ClosedStates.kept().walksIn(counting(comparisons));

        List<Map.Entry<String, ExactRatio>> first = walks.apply(form("c", "3", "a", "1", "b", "5"));
        int afterTheFirst = comparisons.get();
        List<Map.Entry<String, ExactRatio>> second =
                walks.apply(form("b", "5", "c", "3", "a", "1"));

        assertEquals(afterTheFirst, comparisons.get());
        assertEquals(first, second);
    }

    @Test
    void whatIsKeptIsTheWalkTheFormGives() {
        Random dice = new Random(2680);
        List<String> positions = List.of("a", "b", "cc", "x", "y", "zz", "m", "n");
        ClosedStates kept = ClosedStates.kept();
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        Function<CanonicalForm<String>, List<Map.Entry<String, ExactRatio>>> walks =
                kept.walksIn(order);
        for (int round = 0; round < 300; round++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            int howMany = 1 + dice.nextInt(positions.size());
            for (int at = 0; at < howMany; at++) {
                coefs.put(positions.get(dice.nextInt(positions.size())),
                        ExactRatio.of((dice.nextBoolean() ? 1L : -1L) * (1 + dice.nextInt(7))));
            }
            CanonicalForm<String> form = new CanonicalForm<>(coefs);

            assertEquals(form.entriesIn(order), walks.apply(form), "asked first");
            assertEquals(form.entriesIn(order), walks.apply(form), "asked again");
        }
    }

    /** The same form under another order is another walk: what was kept for one is not handed to
     *  the other. */
    @Test
    void anotherOrderIsAnotherWalk() {
        ClosedStates kept = ClosedStates.kept();
        CanonicalOrder<String> forwards = CanonicalOrder.asTheyAreSpelled();
        CanonicalOrder<String> backwards = (one, other) -> other.compareTo(one);
        CanonicalForm<String> form = form("c", "3", "a", "1", "b", "5");

        List<Map.Entry<String, ExactRatio>> up = kept.walksIn(forwards).apply(form);
        List<Map.Entry<String, ExactRatio>> down = kept.walksIn(backwards).apply(form);

        assertEquals(List.of("a", "b", "c"), up.stream().map(Map.Entry::getKey).toList());
        assertEquals(List.of("c", "b", "a"), down.stream().map(Map.Entry::getKey).toList());
        assertEquals(up, kept.walksIn(forwards).apply(form));
        assertEquals(down, kept.walksIn(backwards).apply(form));
    }

    /** Two positions an order cannot tell apart are refused as they are by the form, each time. */
    @Test
    void aWalkThatIsRefusedIsRefusedEachTimeItIsAsked() {
        CanonicalOrder<String> byLength = (one, other) -> Integer.compare(one.length(),
                other.length());
        Function<CanonicalForm<String>, List<Map.Entry<String, ExactRatio>>> walks =
                ClosedStates.kept().walksIn(byLength);
        CanonicalForm<String> tied = form("a", "1", "b", "1");

        assertThrows(IllegalStateException.class, () -> walks.apply(tied));
        assertThrows(IllegalStateException.class, () -> walks.apply(tied));
    }

    @Test
    void aTableThatKeepsNothingWalksTheFormEachTime() {
        AtomicInteger comparisons = new AtomicInteger();
        Function<CanonicalForm<String>, List<Map.Entry<String, ExactRatio>>> walks =
                ClosedStates.NONE.walksIn(counting(comparisons));
        CanonicalForm<String> form = form("c", "3", "a", "1", "b", "5");

        List<Map.Entry<String, ExactRatio>> first = walks.apply(form);
        int afterTheFirst = comparisons.get();
        List<Map.Entry<String, ExactRatio>> second = walks.apply(form);

        assertEquals(2 * afterTheFirst, comparisons.get());
        assertEquals(first, second);
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
