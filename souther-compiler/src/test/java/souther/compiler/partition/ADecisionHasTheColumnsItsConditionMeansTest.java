package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The rules of a decision are the ways its condition can come out, which is what the condition
 * means and not how many times or in what order it is written.
 *
 * <p>Three shapes the meaning settles and the spelling does not. Two conjuncts the other way round
 * are one condition, though a run evaluates them in a different order. A condition written twice
 * on either side of an `||` is the condition once. And a comparison inside the function value a
 * quantifier is handed is not a column of its own: it is asked once per element, and what the
 * decision turns on is whether some element holds it.
 */
class ADecisionHasTheColumnsItsConditionMeansTest {

    private static final String MODEL = """
            module probe

            data Box = { a: Int, b: Int, xs: List<Int> }

            behavior both : (x: Box) -> Int
            let both (x) = if x.a > 0 && x.b > 0 then 2 else 1

            behavior bothTheOtherWay : (x: Box) -> Int
            let bothTheOtherWay (x) = if x.b > 0 && x.a > 0 then 2 else 1

            behavior once : (x: Box) -> Int
            let once (x) = if x.a > 0 then 2 else 1

            behavior twice : (x: Box) -> Int
            let twice (x) = if x.a > 0 || x.a > 0 then 2 else 1

            behavior some : (x: Box) -> Int
            let some (x) = if List.any(e -> e > 0, x.xs) then 2 else 1
            """;

    private static Map<String, Integer> rulesOf(String... behaviors) {
        Map<String, Integer> out = new TreeMap<>();
        for (String each : behaviors) {
            out.put(each, DecisionReadings.readToTheEnd(MODEL, each).size());
        }
        return out;
    }

    @Test
    void twoConjunctsTheOtherWayRoundAreOneCondition() {
        assertEquals(Map.of("both", 3, "bothTheOtherWay", 3), rulesOf("both", "bothTheOtherWay"),
                "both true, or the first that comes out false, whichever is written first");
    }

    @Test
    void aConditionWrittenTwiceIsTheConditionOnce() {
        assertEquals(Map.of("once", 2, "twice", 2), rulesOf("once", "twice"),
                "the second `x.a > 0` comes out as the first did, so it adds no way");
    }

    @Test
    void aComparisonAQuantifierAsksOfEachElementIsNoColumnOfItsOwn() {
        assertEquals(Map.of("some", 2), rulesOf("some"),
                "some element holds it or none does, and nothing about any one element");
    }
}
