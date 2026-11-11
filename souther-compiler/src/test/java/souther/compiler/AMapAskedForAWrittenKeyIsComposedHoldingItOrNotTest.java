package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.DecisionRule;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A guard asking a map for a key the source wrote is composed with the map holding that key, and
 * with the map holding none, as one asking for a key another value of the row names is.
 *
 * <p>The key stands at no position, so nothing is read off the row for it: what the row has to do
 * is to hold the value, or not to hold it, in the map.
 */
class AMapAskedForAWrittenKeyIsComposedHoldingItOrNotTest {

    private static final String MODEL = """
            module probe

            data Priced = { n: Int }
            data Unpriced = { n: Int }

            behavior named : (rates: Map<String, Int>, other: Set<Int>) -> Priced | Unpriced
                constructs Priced, Unpriced

            let named (rates, other) = {
                guard GUARD
                    else Unpriced { n = 0 }
                Priced { n = 1 }
            }
            """;

    /** The same over a map keyed by a newtype, whose constructor a guard writes the key with. */
    private static final String NEWTYPE_MODEL = """
            module probe

            data Code = String

            let usdCode = Code("USD")

            data Priced = { n: Int }
            data Unpriced = { n: Int }

            behavior named : (coded: Map<Code, Int>) -> Priced | Unpriced
                constructs Priced, Unpriced, Code

            let named (coded) = {
                guard GUARD
                    else Unpriced { n = 0 }
                Priced { n = 1 }
            }
            """;

    @Test
    void aMapIsComposedHoldingTheKeyAndNotHoldingIt() {
        assertEquals(List.of(), whatNothingCouldShow("Map.containsKey(\"USD\", rates)"));
        assertEquals(List.of(), whatNothingCouldShow("Bool.not(Map.containsKey(\"USD\", rates))"));
    }

    /** A key a newtype's constructor writes is the value it wraps, at the place that wears the
     *  newtype, written directly or under a name. */
    @Test
    void aMapKeyedByANewtypeIsComposedHoldingTheKeyWrittenAndNotHoldingIt() {
        for (String key : List.of("Code(\"USD\")", "usdCode")) {
            for (String guard : List.of("Map.containsKey(" + key + ", coded)",
                    "Bool.not(Map.containsKey(" + key + ", coded))")) {
                assertEquals(List.of(), DecisionRulesTheSearchLeftUnsettled.notShownIn(
                        NEWTYPE_MODEL.replace("GUARD", guard), "probe"), guard);
            }
        }
    }

    @Test
    void aSetIsComposedHoldingTheValueAndNotHoldingIt() {
        assertEquals(List.of(), whatNothingCouldShow("Set.contains(7, other)"));
        assertEquals(List.of(), whatNothingCouldShow("Bool.not(Set.contains(7, other))"));
    }

    /**
     * A type whose rule asks a container for a value the rule writes is composed holding it, as
     * one whose rule asks for the value at another place is: what the rule asks is that the
     * container hold the member, and a member written is as much one as a member named.
     */
    @Test
    void aTypeWhoseRuleAsksForAWrittenMemberIsComposedHoldingIt() {
        for (List<String> each : List.of(
                List.of("Map<String, Int>", "Map.containsKey(\"USD\", c)", ""),
                List.of("List<String>", "List.contains(\"USD\", c)", ""),
                List.of("Set<Int>", "Set.contains(7, c)", ""))) {
            String model = """
                    module probe

                    %3$s

                    data Box = { c: %1$s, k: Int }
                        invariant %2$s

                    data Priced = { n: Int }
                    data Unpriced = { n: Int }

                    behavior named : (x: Box) -> Priced | Unpriced
                        constructs Priced, Unpriced

                    let named (x) = {
                        guard x.k >= 2
                            else Unpriced { n = 0 }
                        Priced { n = 1 }
                    }
                    """.formatted(each.get(0), each.get(1), each.get(2));

            assertEquals(List.of(), DecisionRulesTheSearchLeftUnsettled.notShownIn(model, "probe"),
                    each.get(1));
        }
    }

    /** The rules of the decision no search could settle. */
    private static List<DecisionRule> whatNothingCouldShow(String guard) {
        return DecisionRulesTheSearchLeftUnsettled.notShownIn(MODEL.replace("GUARD", guard),
                "probe");
    }
}
