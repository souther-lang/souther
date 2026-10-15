package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
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
}
