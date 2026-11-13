package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An order that walks the positions it holds places for by those places puts every walk in the order
 * the order itself does, and a walk of positions it holds places for compares none of them.
 *
 * <p>The first is held against the order as the oracle over drawn sets of positions, some of them
 * naming a position the places do not hold, which is the order's own walk. The second is held by
 * counting the comparisons the order is asked for: a walk that fell back to the order for every
 * form would be the same walk and cost what it cost before.
 */
class APlacedOrderWalksAsItsOrderWalksWithoutComparingTest {

    private static final AtomicInteger COMPARED = new AtomicInteger();

    /** By length, then by spelling: an order that is not the spelling order, so that agreeing with
     *  it is not agreeing with the natural order of the strings. */
    private static final CanonicalOrder<String> BY_LENGTH = (one, other) -> {
        COMPARED.incrementAndGet();
        int by = Integer.compare(one.length(), other.length());
        return by != 0 ? by : one.compareTo(other);
    };

    private static List<String> universe(Random random, int size) {
        Set<String> out = new LinkedHashSet<>();
        while (out.size() < size) {
            StringBuilder name = new StringBuilder();
            for (int at = 0, length = 1 + random.nextInt(4); at < length; at++) {
                name.append((char) ('a' + random.nextInt(6)));
            }
            out.add(name.toString());
        }
        return new ArrayList<>(out);
    }

    private static Map<String, ExactRatio> formOver(List<String> names, Random random) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (String name : names) {
            out.put(name, ExactRatio.of(1 + random.nextInt(5)));
        }
        return out;
    }

    private static List<String> keysOf(List<Map.Entry<String, ExactRatio>> walk) {
        return walk.stream().map(Map.Entry::getKey).toList();
    }

    @Test
    void aWalkOfPlacedPositionsIsTheOrdersWalkAndAWalkNamingAnotherIsTheOrdersOwn() {
        Random random = new Random(3167);
        for (int round = 0; round < 200; round++) {
            List<String> all = universe(random, 12);
            List<String> placed = all.subList(0, 9);
            PlacedOrder<String> order = new PlacedOrder<>(
                    () -> ClosureQuestion.placesIn(new LinkedHashSet<>(placed), BY_LENGTH),
                    BY_LENGTH);
            for (int each = 0; each < 20; each++) {
                List<String> names = new ArrayList<>(all);
                Collections.shuffle(names, random);
                names = names.subList(0, 1 + random.nextInt(all.size()));
                Map<String, ExactRatio> form = formOver(names, random);
                assertEquals(
                        keysOf(BY_LENGTH.walking(form.entrySet(), Map.Entry::getKey)),
                        keysOf(order.walking(form.entrySet(), Map.Entry::getKey)),
                        "a walk of " + names + " placed by " + placed);
            }
        }
    }

    @Test
    void aWalkOfPlacedPositionsAsksTheOrderForNoComparison() {
        List<String> names = universe(new Random(7), 30);
        PlacedOrder<String> order = new PlacedOrder<>(
                () -> ClosureQuestion.placesIn(new LinkedHashSet<>(names), BY_LENGTH), BY_LENGTH);
        Map<String, ExactRatio> form = formOver(names, new Random(8));
        // The places are worked out by the first walk, which compares; what is held is the next.
        order.walking(form.entrySet(), Map.Entry::getKey);
        COMPARED.set(0);
        List<String> walked = keysOf(order.walking(form.entrySet(), Map.Entry::getKey));
        assertEquals(0, COMPARED.get(), "comparisons asked of the order by a walk of placed positions");
        assertEquals(names.size(), walked.size());
        COMPARED.set(0);
        BY_LENGTH.walking(form.entrySet(), Map.Entry::getKey);
        assertTrue(COMPARED.get() > 0, "the order the walk is held against does compare");
    }

    @Test
    void thePlacesAreAskedForByTheFirstWalkOfTwoPositionsAndOnlyOnce() {
        List<String> names = universe(new Random(11), 10);
        AtomicInteger asked = new AtomicInteger();
        PlacedOrder<String> order = new PlacedOrder<>(() -> {
            asked.incrementAndGet();
            return ClosureQuestion.placesIn(new LinkedHashSet<>(names), BY_LENGTH);
        }, BY_LENGTH);

        order.walking(formOver(names.subList(0, 1), new Random(1)).entrySet(), Map.Entry::getKey);
        order.walking(Map.<String, ExactRatio>of().entrySet(), Map.Entry::getKey);
        assertEquals(0, asked.get(), "places asked for by a walk with no two positions to put in order");

        order.walking(formOver(names, new Random(2)).entrySet(), Map.Entry::getKey);
        order.walking(formOver(names, new Random(3)).entrySet(), Map.Entry::getKey);
        assertEquals(1, asked.get(), "places asked for once for every walk of two positions or more");
    }

    @Test
    void twoPositionsTheOrderCannotTellApartAreRefusedWhetherOrNotTheyAreWalkedByPlaces() {
        CanonicalOrder<String> byLengthOnly = (one, other) -> Integer.compare(one.length(), other.length());
        Map<String, ExactRatio> form = new LinkedHashMap<>();
        form.put("ab", ExactRatio.ONE);
        form.put("cd", ExactRatio.ONE);
        PlacedOrder<String> order = new PlacedOrder<>(
                () -> ClosureQuestion.placesIn(new LinkedHashSet<>(form.keySet()), byLengthOnly),
                byLengthOnly);
        assertThrows(IllegalStateException.class,
                () -> byLengthOnly.walking(form.entrySet(), Map.Entry::getKey));
        assertThrows(IllegalStateException.class,
                () -> order.walking(form.entrySet(), Map.Entry::getKey));
    }
}
