package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a form runs between does not turn on the order its coefficients arrive in.
 *
 * <p>Held where the order could decide it. The sums are exact, and an exact sum can fail part of
 * the way: two terms whose scales are far enough apart are a whole number past what the host
 * holds, while the same two beside a term that cancels the larger come to the smaller. So a form
 * weighing three positions that way, each position at one, comes to a value added one way and to
 * nothing found added another — and the order a caller's map iterates in is a hash table's, or a
 * copy's that changes from run to run.
 */
class AFormIsSummedInTheOrderItsPositionsDecideTest {

    private static final ExactRatio HUGE = ExactRatio.of(new BigDecimal("1e1500000000"));
    private static final ExactRatio TINY = ExactRatio.of(new BigDecimal("1e-1500000000"));

    @Test
    void theFormComesToOneAnswerWhicheverOrderItArrivesIn() {
        Map<String, ExactCut> one = new LinkedHashMap<>();
        for (String each : List.of("a", "b", "c")) {
            one.put(each, ExactCut.inclusive(ExactRatio.of(1)));
        }
        Box<String> ends = new Box<>(one, one);
        FormReach<String> reading = FormReach.over(List.of(), ends,
                DifferenceBounds.over(List.of(), CanonicalOrder.asTheyAreSpelled()),
                CanonicalOrder.asTheyAreSpelled());

        Map<String, ExactRatio> cancellingFirst = new LinkedHashMap<>();
        cancellingFirst.put("a", HUGE);
        cancellingFirst.put("b", HUGE.negated());
        cancellingFirst.put("c", TINY);
        Map<String, ExactRatio> apartFirst = new LinkedHashMap<>();
        apartFirst.put("a", HUGE);
        apartFirst.put("c", TINY);
        apartFirst.put("b", HUGE.negated());

        Reach one1 = reading.of(cancellingFirst, ExactRatio.ZERO);
        Reach one2 = reading.of(apartFirst, ExactRatio.ZERO);

        assertEquals(one1, one2, "the order the coefficients arrived in decides nothing");
        assertNotNull(one1.most(), "and in the order the positions decide, the sum is held: "
                + one1);
    }

    /**
     * Terms of one size and opposite signs have no order among them that sorting by size could
     * give: {@code H + H} is past what is held where {@code H - H} is nought, and which of the two
     * a name order meets first is the names'. The sum is the one sum under every way of weighing
     * four positions by {@code H, H, -H, -H}.
     */
    @Test
    void termsOfOneSizeAndOppositeSignsSumToOneAnswerWhateverTheyAreCalled() {
        ExactRatio large = new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MAX_VALUE, 0);
        assertEquals(false, large.plus(large).orNull() != null, "twice it is past what is held");
        List<String> names = List.of("a", "b", "c", "d");
        List<ExactRatio> weights = List.of(large, large, large.negated(), large.negated());
        Map<String, ExactCut> ends = new LinkedHashMap<>();
        names.forEach(each -> ends.put(each, ExactCut.inclusive(ExactRatio.of(1))));
        FormReach<String> reading = FormReach.over(List.of(), new Box<>(ends, ends),
                DifferenceBounds.over(List.of(), CanonicalOrder.asTheyAreSpelled()),
                CanonicalOrder.asTheyAreSpelled());
        for (List<Integer> order : permutations(List.of(0, 1, 2, 3))) {
            Map<String, ExactRatio> weighing = new LinkedHashMap<>();
            for (int at = 0; at < 4; at++) {
                weighing.put(names.get(at), weights.get(order.get(at)));
            }

            Reach reach = reading.of(weighing, ExactRatio.ZERO);

            assertEquals(ExactRatio.ZERO, reach.most().at(), "under " + order);
        }
    }

    private static List<List<Integer>> permutations(List<Integer> of) {
        if (of.size() <= 1) {
            return List.of(of);
        }
        List<List<Integer>> out = new ArrayList<>();
        for (int at = 0; at < of.size(); at++) {
            List<Integer> rest = new ArrayList<>(of);
            Integer head = rest.remove(at);
            for (List<Integer> tail : permutations(rest)) {
                List<Integer> one = new ArrayList<>();
                one.add(head);
                one.addAll(tail);
                out.add(one);
            }
        }
        return out;
    }

    /**
     * The order the positions decide is the order of their names, so the same form over the same
     * ends with the positions called other things is the same sum met in another order. What it
     * runs between is the same under each of the six ways of calling them.
     */
    @Test
    void theFormComesToOneAnswerWhateverThePositionsAreCalled() {
        List<List<String>> namings = List.of(List.of("a", "b", "c"), List.of("a", "c", "b"),
                List.of("b", "a", "c"), List.of("b", "c", "a"), List.of("c", "a", "b"),
                List.of("c", "b", "a"));
        Reach first = null;
        for (List<String> names : namings) {
            Map<String, ExactCut> one = new LinkedHashMap<>();
            for (String each : names) {
                one.put(each, ExactCut.inclusive(ExactRatio.of(1)));
            }
            FormReach<String> reading = FormReach.over(List.of(), new Box<>(one, one),
                    DifferenceBounds.over(List.of(), CanonicalOrder.asTheyAreSpelled()),
                    CanonicalOrder.asTheyAreSpelled());
            Map<String, ExactRatio> weighing = new LinkedHashMap<>();
            weighing.put(names.get(0), HUGE);
            weighing.put(names.get(1), HUGE.negated());
            weighing.put(names.get(2), TINY);

            Reach reach = reading.of(weighing, ExactRatio.ZERO);

            assertNotNull(reach.most(), "the sum is held under " + names + ": " + reach);
            if (first == null) {
                first = reach;
            }
            assertEquals(first, reach, "and comes to the same under " + names);
        }
    }
}
