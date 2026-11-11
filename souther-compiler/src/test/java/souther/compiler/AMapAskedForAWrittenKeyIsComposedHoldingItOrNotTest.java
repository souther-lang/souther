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

    @Test
    void aMapIsComposedHoldingTheKeyAndNotHoldingIt() {
        assertEquals(List.of(), whatNothingCouldShow("Map.containsKey(\"USD\", rates)"));
        assertEquals(List.of(), whatNothingCouldShow("Bool.not(Map.containsKey(\"USD\", rates))"));
    }

    @Test
    void aSetIsComposedHoldingTheValueAndNotHoldingIt() {
        assertEquals(List.of(), whatNothingCouldShow("Set.contains(7, other)"));
        assertEquals(List.of(), whatNothingCouldShow("Bool.not(Set.contains(7, other))"));
    }

    /** The rules of the decision no search could settle. */
    private static List<DecisionRule> whatNothingCouldShow(String guard) {
        return DecisionRulesTheSearchLeftUnsettled.notShownIn(MODEL.replace("GUARD", guard),
                "probe");
    }
}
