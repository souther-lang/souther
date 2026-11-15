package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The values a guard keeps from a relation are left open by the relation, and which types its two
 * sides are declared as does not decide it: a side is parted or not by what the other can hold, and
 * the lengths the run gets to the relation at are carried whether or not it is.
 */
class AGuardKeepsValuesFromARelationWhateverTheTypesOfItsSidesTest {

    private static final String TYPES = """
            data T = String
                invariant String.matches("[a-z ]+", value) && String.length(value) <= 100

            data B = String
                invariant String.length(value) >= 1
            """;

    private static String trimmedGuard(String a, String b) {
        return "module e5\n" + TYPES + """

                behavior f : (a: %s, b: %s) -> Int
                    constructs B

                let f (a, b) = {
                    guard B(String.trim(%s)) as t else 0
                    if %s == %s then 1 else 2
                }
                """.formatted(a, b, a.equals("T") ? "a.value" : "a",
                a.equals("T") ? "a.value" : "a", b.equals("T") ? "b.value" : "b");
    }

    private static String lengthGuard(String a, String b) {
        String av = a.equals("T") ? "a.value" : "a";
        String bv = b.equals("T") ? "b.value" : "b";
        return "module e2\n" + TYPES + """

                behavior f : (a: %s, b: %s) -> Int
                let f (a, b) = {
                    guard String.length(%s) >= 3 else 0
                    if %s == %s then 1 else 2
                }
                """.formatted(a, b, av, av, bv);
    }

    private static List<BlockReason.RelationShownOverARegion> openAtA(String source) {
        return WhereAStringRelationIsLeftOpen.leftOpen(source, "f").getOrDefault("a", List.of());
    }

    @Test
    void aGuardOnWhatIsLeftOfTheTrimmedStringLeavesTheBlankOnesOpenForEveryTypeOfTheSides() {
        for (String a : List.of("T", "String")) {
            for (String b : List.of("T", "String")) {
                List<BlockReason.RelationShownOverARegion> open =
                        openAtA(trimmedGuard(a, b));
                assertEquals(1, open.size(), a + " " + b + " " + open);
                assertEquals(1, open.getFirst().byCodePoints().size(), a + " " + b + " " + open);
            }
        }
    }

    @Test
    void aGuardOnTheLengthLeavesTheShortStringsOpenForEveryTypeOfTheSides() {
        for (String a : List.of("T", "String")) {
            for (String b : List.of("T", "String")) {
                List<BlockReason.RelationShownOverARegion> open =
                        openAtA(lengthGuard(a, b));
                assertEquals(List.of(3L), open.stream().map(each -> each.shorterThan()).toList(),
                        a + " " + b + " " + open);
            }
        }
    }

    /** Beside the control: the same models with no guard leave nothing of {@code a} open. */
    @Test
    void withNoGuardNothingIsKeptFromTheRelation() {
        assertEquals(Map.of(), WhereAStringRelationIsLeftOpen.leftOpen("""
                module c

                behavior f : (a: String, b: String) -> Int
                let f (a, b) = if a == b then 1 else 2
                """, "f"));
    }
}
