package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rules prove of a goal is still proved when rules are added that name none of the
 * positions the goal, or the rules it depends on, name. The ways of solving the equalities are
 * counted over the rules a goal reaches, so equalities elsewhere cannot make them too many.
 */
class AnEqualityNoGoalNamesDoesNotCostAProofTest {

    private static final int HOW_MANY = 6;

    private static LinearForm<String> sum(String total, String... parts) {
        LinearForm<String> out = LinearForm.<String>atom(total);
        for (String part : parts) {
            out = out.minus(LinearForm.<String>atom(part)).orNull();
        }
        return out;
    }

    private static NumericDomain<String> domainWith(int unrelated, boolean joined) {
        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        for (String each : new String[] {"x", "y", "a", "b", "c", "d"}) {
            spaces.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        for (int i = 0; i < unrelated; i++) {
            for (String each : new String[] {"u", "v", "w"}) {
                spaces.put(each + i, NumberSpace.spacedOnly(Granularity.DISCRETE));
            }
        }
        NumericDomain<String> out = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        out = out.assume(sum("x", "a", "b"), Rel.EQ, spaces);
        out = out.assume(sum("y", "a", "b"), Rel.EQ, spaces);
        if (joined) {
            out = out.assume(sum("c", "x", "d"), Rel.EQ, spaces);
        }
        for (int i = 0; i < unrelated; i++) {
            out = out.assume(sum("u" + i, "v" + i, "w" + i), Rel.EQ, spaces);
        }
        return out;
    }

    @Test
    void aProofIsKeptWhateverUnrelatedEqualitiesAreAdded() {
        for (int unrelated = 0; unrelated <= HOW_MANY; unrelated++) {
            NumericDomain<String> domain = domainWith(unrelated, false);

            assertTrue(domain.entails(sum("x", "y"), Rel.EQ),
                    "x = y is proved with " + unrelated + " unrelated equalities");
        }
    }

    /**
     * Equalities that name a position the goal's equalities name are in the same part as them and
     * are no more needed: {@code a = p + q} says nothing of {@code x = y}. However many of them
     * there are, what the equalities come to together proves it.
     */
    @Test
    void aProofIsKeptWhateverEqualitiesJoinedToItsOwnAreAdded() {
        for (int joined = 0; joined <= HOW_MANY + 1; joined++) {
            Map<String, NumberSpace> spaces = new LinkedHashMap<>();
            for (String each : new String[] {"x", "y", "a", "b"}) {
                spaces.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
            }
            for (int i = 0; i < joined; i++) {
                spaces.put("p" + i, NumberSpace.spacedOnly(Granularity.DISCRETE));
                spaces.put("q" + i, NumberSpace.spacedOnly(Granularity.DISCRETE));
            }
            NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
            domain = domain.assume(sum("x", "a", "b"), Rel.EQ, spaces);
            domain = domain.assume(sum("y", "a", "b"), Rel.EQ, spaces);
            for (int i = 0; i < joined; i++) {
                domain = domain.assume(sum("a", "p" + i, "q" + i), Rel.EQ, spaces);
            }

            assertTrue(domain.entails(sum("x", "y"), Rel.EQ),
                    "x = y is proved beside " + joined + " equalities joined to it");
        }
    }

    @Test
    void aProofOverEqualitiesJoinedToEachOtherIsKeptToo() {
        for (int unrelated = 0; unrelated <= HOW_MANY; unrelated++) {
            NumericDomain<String> domain = domainWith(unrelated, true);

            assertTrue(domain.entails(sum("y", "c", "d").minus(LinearForm.<String>atom("x")
                            .minus(LinearForm.<String>atom("c")).orNull()).orNull(), Rel.EQ)
                            || domain.entails(sum("x", "y"), Rel.EQ),
                    "with " + unrelated + " unrelated equalities");
        }
    }

    @Test
    void aGoalOverTwoSetsOfEqualitiesIsProvedWhateverElseIsAdded() {
        for (int unrelated = 0; unrelated <= HOW_MANY; unrelated++) {
            Map<String, NumberSpace> spaces = new LinkedHashMap<>();
            for (String each : new String[] {"x", "y", "a", "b", "c", "d"}) {
                spaces.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
            }
            for (int i = 0; i < unrelated; i++) {
                for (String each : new String[] {"u", "v", "w"}) {
                    spaces.put(each + i, NumberSpace.spacedOnly(Granularity.DISCRETE));
                }
            }
            NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
            domain = domain.assume(sum("x", "a", "b"), Rel.EQ, spaces);
            domain = domain.assume(sum("y", "c", "d"), Rel.EQ, spaces);
            for (int i = 0; i < unrelated; i++) {
                domain = domain.assume(sum("u" + i, "v" + i, "w" + i), Rel.EQ, spaces);
            }

            assertTrue(domain.entails(sum("x", "a", "b").plus(sum("y", "c", "d")).orNull(), Rel.EQ),
                    "with " + unrelated + " unrelated equalities");
        }
    }
}
