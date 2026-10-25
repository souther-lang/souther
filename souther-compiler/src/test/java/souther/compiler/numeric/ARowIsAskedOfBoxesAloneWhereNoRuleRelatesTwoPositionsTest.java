package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where every rule bounds one position, whether the rules leave a row is what the boxes and the
 * orders say, and is the answer taking the ends in as rules and closing again gives.
 *
 * <p>Enumerated at random over rules of the shape {@code k·x + c rel 0} with the orders nought to
 * seven, spaced as whole numbers and as a continuum, so the strict bounds that step and the ones
 * that do not are both asked. The boxes decide it without the second closure, which is the cost
 * this shape does not need to pay.
 */
class ARowIsAskedOfBoxesAloneWhereNoRuleRelatesTwoPositionsTest {

    private static final List<String> ATOMS = List.of("a", "b", "c");
    private static final Rel[] RELS = {Rel.GE, Rel.GT, Rel.LE, Rel.LT, Rel.EQ};
    private static final long[] COEFS = {1, 2, 3, -1, -2};

    private static NumericDomain<String> random(Random random, Granularity spacing) {
        NumberSpace seven = new NumberSpace(spacing, new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(0)), Endpoint.inclusive(Count.of(7))));
        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        ATOMS.forEach(each -> spaces.put(each, seven));
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.<String>asTheyAreSpelled());
        int rules = 1 + random.nextInt(4);
        for (int i = 0; i < rules; i++) {
            String atom = ATOMS.get(random.nextInt(ATOMS.size()));
            long coef = COEFS[random.nextInt(COEFS.length)];
            LinearForm<String> form = LinearForm.<String>atom(atom);
            for (long k = 1; k < Math.abs(coef); k++) {
                form = form.plus(LinearForm.atom(atom)).orNull();
            }
            if (coef < 0) {
                form = LinearForm.<String>constant(ExactRatio.ZERO).minus(form).orNull();
            }
            form = form.minus(LinearForm.constant(ExactRatio.of(random.nextInt(31) - 12))).orNull();
            domain = domain.assumeWithin(form, RELS[random.nextInt(RELS.length)], spaces);
        }
        return domain;
    }

    @Test
    void theBoxesAnswerWhatTheClosureWithTheEndsAnswers() {
        Random random = new Random(2705);
        List<String> differed = new ArrayList<>();
        int none = 0;
        for (Granularity spacing : Granularity.values()) {
            for (int s = 0; s < 4000; s++) {
                NumericDomain<String> domain = random(random, spacing);
                boolean byClosure = domain.isBottom() || domain.leavesNoRowByClosure();
                none += byClosure ? 1 : 0;
                if (domain.leavesNoRow() != byClosure) {
                    differed.add(spacing + " " + domain.rulesRead() + " boxes="
                            + domain.leavesNoRow() + " closure=" + byClosure);
                }
            }
        }
        assertEquals(List.of(), differed.stream().limit(5).toList());
        assertTrue(none > 200, "the sample must hold systems that leave no row: " + none);
    }
}
