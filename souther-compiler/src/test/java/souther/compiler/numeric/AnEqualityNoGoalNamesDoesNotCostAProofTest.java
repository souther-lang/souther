package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
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

            // c = x + d and x = y say c - y - d is nought; x = y alone does not say it.
            assertTrue(domain.entails(sum("c", "y", "d"), Rel.EQ),
                    "with " + unrelated + " unrelated equalities");
        }
    }

    private static Map<String, NumberSpace> spacesOf(List<String> names) {
        Map<String, NumberSpace> spaces = new LinkedHashMap<>();
        names.forEach(each -> spaces.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE)));
        return spaces;
    }

    /**
     * A chain of equalities joined to the proof's own at {@code a} is as long as anyone writes it:
     * what the equalities come to together is read without the work growing with the square of the
     * chain, and the equalities of the proof are among what is read.
     */
    @Test
    void aProofIsKeptBesideALongChainJoinedToIt() {
        int length = 150;
        List<String> names = new ArrayList<>(List.of("x", "y", "a", "b"));
        for (int i = 0; i <= length; i++) {
            names.add("p" + i);
            names.add("q" + i);
        }
        Map<String, NumberSpace> spaces = spacesOf(names);
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        domain = domain.assume(sum("x", "a", "b"), Rel.EQ, spaces);
        domain = domain.assume(sum("y", "a", "b"), Rel.EQ, spaces);
        domain = domain.assume(sum("a", "p0", "q0"), Rel.EQ, spaces);
        for (int i = 0; i < length; i++) {
            domain = domain.assume(sum("p" + i, "p" + (i + 1), "q" + (i + 1)), Rel.EQ, spaces);
        }

        assertTrue(domain.entails(sum("x", "y"), Rel.EQ));
    }

    /**
     * Equalities each a combination of two others add nothing and are not a level of anything: a
     * great many of them neither overflow the stack nor take the proof of what the two say.
     */
    @Test
    void equalitiesThatAreCombinationsOfOthersAreNoDepth() {
        Map<String, NumberSpace> spaces = spacesOf(List.of("x", "y", "z"));
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        LinearForm<String> all = LinearForm.<String>atom("x")
                .plus(LinearForm.<String>atom("y")).orNull()
                .plus(LinearForm.<String>atom("z")).orNull();
        domain = domain.assume(all, Rel.EQ, spaces);
        domain = domain.assume(sum("x", "y"), Rel.EQ, spaces);
        // More than the descent looking for the ways of choosing is held to.
        for (int k = 2; k < ReducedRules.MOST_EQUATIONS + 40; k++) {
            LinearForm<String> combination = LinearForm.<String>atom("x")
                    .times(ExactRatio.of(k + 1)).orNull()
                    .plus(LinearForm.<String>atom("y").times(ExactRatio.of(1 - k)).orNull())
                    .orNull()
                    .plus(LinearForm.<String>atom("z")).orNull();
            domain = domain.assume(combination, Rel.EQ, spaces);
        }

        // x + y + z = 0 and x = y: z + 2x is their sum with nothing else.
        assertTrue(domain.entails(LinearForm.<String>atom("z")
                .plus(LinearForm.<String>atom("x").times(ExactRatio.of(2)).orNull()).orNull(),
                Rel.EQ));
    }

    /**
     * A goal over several parts is a sum of one piece for each, and each piece is bounded by its
     * own part: the bounds add up where asking every combination of the ways of each would be more
     * than any bound on the ways allows.
     */
    @Test
    void aGoalOverSeveralPartsIsProvedByTheBoundOfEachPart() {
        int parts = 4;
        List<String> names = new ArrayList<>();
        for (int i = 0; i < parts; i++) {
            names.addAll(List.of("t" + i, "m" + i, "n" + i));
        }
        Map<String, NumberSpace> spaces = spacesOf(names);
        NumericDomain<String> domain = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        LinearForm<String> goal = LinearForm.constant(ExactRatio.of(-parts));
        for (int i = 0; i < parts; i++) {
            domain = domain.assume(sum("t" + i, "m" + i, "n" + i), Rel.EQ, spaces);
            domain = domain.assume(LinearForm.<String>atom("t" + i)
                    .minus(LinearForm.constant(ExactRatio.ONE)).orNull(), Rel.LE, spaces);
            goal = goal.plus(LinearForm.<String>atom("m" + i)).orNull()
                    .plus(LinearForm.<String>atom("n" + i)).orNull();
        }

        assertTrue(domain.entails(goal, Rel.LE));
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
