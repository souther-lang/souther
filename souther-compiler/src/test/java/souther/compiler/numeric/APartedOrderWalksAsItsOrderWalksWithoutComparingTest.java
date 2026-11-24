package souther.compiler.numeric;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.rule;
import static souther.compiler.numeric.RulesAsWritten.statedOnly;

/**
 * An order that walks the positions of one part by the places that part was asked with puts every
 * walk in the order the order itself does, and a walk of positions of one part compares none of
 * them.
 *
 * <p>The first is held against the order as the oracle over drawn forms: over positions of one
 * part, of two parts, and naming a position of none, which are walked by the order itself. The
 * second is held by counting the comparisons the order is asked for after the parts have been
 * asked: a walk that fell back to the order for every form would be the same walk and cost what it
 * cost before.
 */
class APartedOrderWalksAsItsOrderWalksWithoutComparingTest {

    private static final AtomicInteger COMPARED = new AtomicInteger();

    /** By spelling, counting what it is asked. */
    private static int comparedByCounting(String one, String other) {
        COMPARED.incrementAndGet();
        return one.compareTo(other);
    }

    private static final CanonicalOrder<String> COUNTING =
            APartedOrderWalksAsItsOrderWalksWithoutComparingTest::comparedByCounting;

    private static Granularity whole(String ignored) {
        return Granularity.DISCRETE;
    }

    /** A chain of prefix sums over {@code names}, which is one part of its own. */
    private static List<Written> prefixSumsOver(List<String> names) {
        List<Written> out = new ArrayList<>();
        for (int to = 2; to <= names.size(); to++) {
            out.add(rule(String.join(" + ", names.subList(0, to)) + " <= " + 9 * to));
        }
        return out;
    }

    private static List<String> namesBeginning(String first, int count) {
        List<String> out = new ArrayList<>();
        for (int at = 0; at < count; at++) {
            out.add(first + (char) ('a' + at));
        }
        return out;
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

    private static List<String> walked(CanonicalOrder<String> order, Map<String, ExactRatio> form) {
        return keysOf(order.walking(form.entrySet(), Map.Entry::getKey));
    }

    /** Two parts of rules, and the order that walks them. */
    private record Parts(List<String> first, List<String> second, ClosedStates.Parted<String> parted) {

        static Parts of(CanonicalOrder<String> order) {
            List<String> first = namesBeginning("p", 12);
            List<String> second = namesBeginning("q", 6);
            List<Written> written = new ArrayList<>(prefixSumsOver(first));
            written.addAll(prefixSumsOver(second));
            List<AffineConstraint<String>> rules =
                    statedOnly(written, APartedOrderWalksAsItsOrderWalksWithoutComparingTest::whole);
            return new Parts(first, second, ClosedStates.kept().of(rules,
                    APartedOrderWalksAsItsOrderWalksWithoutComparingTest::whole, order, null));
        }
    }

    @Test
    void aWalkOfPositionsOfOnePartIsTheOrdersWalkAndAWalkOfAnythingElseIsTheOrdersOwn() {
        Random random = new Random(3167);
        Parts parts = Parts.of(COUNTING);
        CanonicalOrder<String> parted = parts.parted().orderedBy(COUNTING);
        List<String> outside = List.of("zzz", "yyy");
        int ofOnePart = 0;
        int ofSeveral = 0;
        for (int round = 0; round < 400; round++) {
            List<String> pool = new ArrayList<>(parts.first());
            pool.addAll(parts.second());
            pool.addAll(outside);
            Collections.shuffle(pool, random);
            List<String> names = pool.subList(0, 1 + random.nextInt(round % 2 == 0 ? 4 : pool.size()));
            Map<String, ExactRatio> form = formOver(names, random);
            assertEquals(walked(COUNTING, form), walked(parted, form), "a walk of " + names);
            if (parts.first().containsAll(names) || parts.second().containsAll(names)) {
                ofOnePart++;
            } else {
                ofSeveral++;
            }
        }
        assertTrue(ofOnePart > 20 && ofSeveral > 20,
                "forms drawn over one part and over others: " + ofOnePart + ", " + ofSeveral);
    }

    @Test
    void aWalkOfPositionsOfOnePartAsksTheOrderForNoComparison() {
        Parts parts = Parts.of(COUNTING);
        CanonicalOrder<String> parted = parts.parted().orderedBy(COUNTING);
        Map<String, ExactRatio> form = formOver(parts.first(), new Random(8));

        COMPARED.set(0);
        List<String> walked = walked(parted, form);
        assertEquals(0, COMPARED.get(), "comparisons asked of the order by a walk of one part");
        assertEquals(parts.first().size(), walked.size());

        COMPARED.set(0);
        walked(COUNTING, form);
        assertTrue(COMPARED.get() > 0, "the order the walk is held against does compare");
    }

    @Test
    void aWalkOfAPartAndOnePositionBesideItIsComparedOnlyWhereTheTwoMeet() {
        Parts parts = Parts.of(COUNTING);
        CanonicalOrder<String> parted = parts.parted().orderedBy(COUNTING);
        List<String> besideTheSecondPart = new ArrayList<>(parts.first());
        besideTheSecondPart.add(parts.second().getFirst());
        List<String> besideNoPart = new ArrayList<>(parts.first());
        besideNoPart.add("zzz");

        for (List<String> names : List.of(besideTheSecondPart, besideNoPart)) {
            Map<String, ExactRatio> form = formOver(names, new Random(1));
            COMPARED.set(0);
            walked(COUNTING, form);
            int byTheOrder = COMPARED.get();
            COMPARED.set(0);
            walked(parted, form);
            int byTheParts = COMPARED.get();
            assertTrue(byTheParts > 0, "the position beside the part was compared with none");
            assertTrue(byTheParts * 3 <= byTheOrder, "comparisons of " + names.size() + " positions, "
                    + "one of them beside the part: " + byTheParts + ", where the order makes "
                    + byTheOrder);
        }
    }

    @Test
    void whereTheRulesWereNotPartedTheOrderIsTheOneHanded() {
        List<AffineConstraint<String>> rules = statedOnly(prefixSumsOver(namesBeginning("p", 4)),
                APartedOrderWalksAsItsOrderWalksWithoutComparingTest::whole);
        for (ClosedStates keeping : List.of(ClosedStates.NONE, ClosedStates.IN_ONE_RUN)) {
            assertSame(COUNTING, keeping.of(rules,
                    APartedOrderWalksAsItsOrderWalksWithoutComparingTest::whole, COUNTING, null)
                    .orderedBy(COUNTING));
        }
    }

    @Test
    void twoPositionsTheOrderCannotTellApartAreRefusedWhereTheRulesAreWalkedInTheOrder() {
        CanonicalOrder<String> byLengthOnly =
                (one, other) -> Integer.compare(one.length(), other.length());
        List<AffineConstraint<String>> rules = statedOnly(List.of(rule("ab + cd <= 9")),
                APartedOrderWalksAsItsOrderWalksWithoutComparingTest::whole);
        Map<String, ExactRatio> form = new LinkedHashMap<>();
        form.put("ab", ExactRatio.ONE);
        form.put("cd", ExactRatio.ONE);

        assertFalse(rules.isEmpty());
        assertThrows(IllegalStateException.class,
                () -> byLengthOnly.walking(form.entrySet(), Map.Entry::getKey));
        // The part is asked with the places of its positions, which is where the pair is refused, so
        // there is no order over its places for a walk to put the pair in.
        assertThrows(IllegalStateException.class, () -> ClosedStates.kept().of(rules,
                APartedOrderWalksAsItsOrderWalksWithoutComparingTest::whole, byLengthOnly, null));
    }
}
