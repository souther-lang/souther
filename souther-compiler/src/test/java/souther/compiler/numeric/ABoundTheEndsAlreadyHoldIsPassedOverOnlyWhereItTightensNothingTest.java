package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A bound on one position that the ends already hold is passed over where the residual it leaves
 * is bounded by the ranges alone, and merged in where the residual is a difference the closed
 * differences hold lower.
 *
 * <p>What it is held against for every other shape is the reading that merges every premise in
 * ({@link APremiseNamingNoneOfAFormIsPassedOverOnlyWhereItCouldTightenNothingTest}). That reading
 * draws its states at random, and a residual whose difference a chain of rules closes tighter than
 * any one rule states is not a state a draw reaches, so it is written out here.
 */
class ABoundTheEndsAlreadyHoldIsPassedOverOnlyWhereItTightensNothingTest {

    /**
     * {@code a - b <= 0} and {@code b - c <= 0} close to {@code a - c <= 0}, which no rule states.
     * Taking {@code a <= 5} off {@code 2a - c} leaves {@code a - c + 5}, which that closed difference
     * holds at five; the ranges hold {@code 2a - c} at ten, and so does every other premise.
     */
    @Test
    void aBoundLeavingADifferenceTheRulesCloseIsMergedIn() {
        List<AffineConstraint<String>> rules = List.of(
                stated(Map.of("a", ExactRatio.of(1), "b", ExactRatio.of(-1)), 0),
                stated(Map.of("b", ExactRatio.of(1), "c", ExactRatio.of(-1)), 0),
                stated(Map.of("a", ExactRatio.of(1)), -5));
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        for (String position : List.of("a", "b", "c")) {
            least.put(position, ExactCut.inclusive(ExactRatio.of(0)));
            most.put(position, ExactCut.inclusive(ExactRatio.of(5)));
        }
        FormReach<String> reading = FormReach.over(rules, new Box<>(least, most),
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled()),
                CanonicalOrder.asTheyAreSpelled());
        Map<String, ExactRatio> form = new LinkedHashMap<>();
        form.put("a", ExactRatio.of(2));
        form.put("c", ExactRatio.of(-1));

        assertEquals(ExactCut.inclusive(ExactRatio.of(5)), reading.most(form, ExactRatio.ZERO));
    }

    /** {@code Σ coefs <= -constant}, as the reading states it. */
    private static AffineConstraint<String> stated(Map<String, ExactRatio> coefs, int constant) {
        Read<String> read = AffineConstraint.of(new LinkedHashMap<>(coefs),
                ExactRatio.of(constant), Rel.LE, atom -> Granularity.DISCRETE);
        return ((Read.Stated<String>) read).constraint();
    }
}
