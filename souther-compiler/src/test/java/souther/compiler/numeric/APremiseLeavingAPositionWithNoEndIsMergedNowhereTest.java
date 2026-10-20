package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A premise whose residual weighs three positions or more, one of them with no end the way its
 * weight runs it up, is merged into no form: the ranges bound that residual nowhere, and they are
 * its only route.
 *
 * <p>Counted, because what the form comes to is the same either way — the reading that merges
 * every premise in holds that ({@link APremiseNamingNoneOfAFormIsPassedOverOnlyWhereItCouldTightenNothingTest})
 * — and what is held here is the work. The bounds an {@code Int} puts on each partial sum of a long
 * addition are rules of this kind over positions with no ends, and merging each into each was most
 * of what reading such a body cost.
 */
class APremiseLeavingAPositionWithNoEndIsMergedNowhereTest {

    /**
     * Over {@code a + b + c} with no ends anywhere, {@code a + d <= 1} leaves {@code b + c - d + 1},
     * three positions with no end, and is passed over. {@code a + b + c + d <= 10} leaves
     * {@code 10 - d}, one position, and is merged in.
     */
    @Test
    void onlyThePremiseLeavingFewerThanThreeIsMergedIn() {
        List<AffineConstraint<String>> rules = List.of(
                stated(Map.of("a", ExactRatio.of(1), "d", ExactRatio.of(1)), -1),
                stated(Map.of("a", ExactRatio.of(1), "b", ExactRatio.of(1),
                        "c", ExactRatio.of(1), "d", ExactRatio.of(1)), -10));
        FormReach<String> reading = FormReach.over(rules, new Box<>(Map.of(), Map.of()),
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled()),
                CanonicalOrder.asTheyAreSpelled());
        Map<String, ExactRatio> form = new LinkedHashMap<>();
        form.put("a", ExactRatio.of(1));
        form.put("b", ExactRatio.of(1));
        form.put("c", ExactRatio.of(1));

        assertNull(reading.most(form, ExactRatio.ZERO));
        assertEquals(1, reading.premisesMerged());
    }

    /** {@code Σ coefs <= -constant}, as the reading states it. */
    private static AffineConstraint<String> stated(Map<String, ExactRatio> coefs, int constant) {
        Read<String> read = AffineConstraint.of(new LinkedHashMap<>(coefs),
                ExactRatio.of(constant), Rel.LE, atom -> Granularity.DISCRETE);
        return ((Read.Stated<String>) read).constraint();
    }
}
