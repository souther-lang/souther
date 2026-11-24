package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.UnaryOperator;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a chain of equalities each naming the next, and a position of its own, comes to is read
 * whatever the positions are called. Which position each equality is solved for is what decides
 * how many weights are updated, and it must not be the order of the names that decides it: a chain
 * as long as the work allows is read under every naming or under none.
 *
 * <p>Each equality is {@code p(i) - p(i+1) - q(i+1) = 0}. Solved for {@code p(i+1)}, every later
 * equality names a position an earlier one was solved for, and the {@code q}s pile up in each of
 * them: the square of the chain in updates. Solved for {@code q(i+1)}, nothing is rewritten.
 */
class AChainOfEqualitiesIsReadWhateverItsPositionsAreCalledTest {

    /** Past what the square of it fits in {@link EqualitySpan#MOST_UPDATES}. */
    private static final int LENGTH = 700;

    private static CanonicalForm<String> form(Map<String, Integer> weights) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((each, weight) -> coefs.put(each, ExactRatio.of(weight)));
        return new CanonicalForm<>(coefs);
    }

    private static List<AffineConstraint<String>> chain(UnaryOperator<String> called) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (int i = 0; i < LENGTH; i++) {
            Map<String, Integer> weights = new LinkedHashMap<>();
            weights.put(called.apply("p" + i), 1);
            weights.put(called.apply("p" + (i + 1)), -1);
            weights.put(called.apply("q" + (i + 1)), -1);
            out.add(new AffineConstraint.Equality<>(form(weights), ExactRatio.ZERO));
        }
        return out;
    }

    /** {@code p(0) - p(LENGTH) - q(1) - ... - q(LENGTH)}, the sum of every equality. */
    private static CanonicalForm<String> everyEquality(UnaryOperator<String> called) {
        Map<String, Integer> weights = new LinkedHashMap<>();
        weights.put(called.apply("p0"), 1);
        weights.put(called.apply("p" + LENGTH), -1);
        for (int i = 1; i <= LENGTH; i++) {
            weights.put(called.apply("q" + i), -1);
        }
        return form(weights);
    }

    private static void assertReadAsNothing(UnaryOperator<String> called, String how) {
        EqualitySpan<String> span =
                EqualitySpan.of(chain(called), CanonicalOrder.asTheyAreSpelled());

        assertNotNull(span, "the chain is read " + how);
        EqualitySpan.Residue<String> left =
                span.residue(everyEquality(called), ExactRatio.ZERO);
        assertNotNull(left, "and a sum of it is read " + how);
        assertTrue(left.coefs().isEmpty() && left.constant().isZero(),
                "the sum of every equality of the chain is nothing " + how + ": " + left);
    }

    @Test
    void theChainIsReadWhicheverEndOfEachEqualityTheNamesPutLast() {
        assertReadAsNothing(each -> (each.startsWith("p") ? "a" : "z") + each.substring(1),
                "with the chain's positions first");
        assertReadAsNothing(each -> (each.startsWith("p") ? "z" : "a") + each.substring(1),
                "with the chain's positions last");
    }

    @Test
    void theChainIsReadUnderNamesInAnyOrder() {
        for (long seed = 1; seed <= 5; seed++) {
            List<String> names = new ArrayList<>();
            for (int i = 0; i <= LENGTH; i++) {
                names.add("p" + i);
                names.add("q" + i);
            }
            List<String> shuffled = new ArrayList<>(names);
            Collections.shuffle(shuffled, new Random(seed));
            Map<String, String> renamed = new LinkedHashMap<>();
            for (int at = 0; at < names.size(); at++) {
                renamed.put(shuffled.get(at), String.format("n%05d", at));
            }
            assertReadAsNothing(renamed::get, "under the naming of seed " + seed);
        }
    }
}
