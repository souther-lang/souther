package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A number the declarations refuse is no point of a border, however close to the line it is.
 *
 * <p>The ends of a range say nothing of the numbers between them. A value held to a class of
 * remainders is refused at every number outside the class, so the number beside a line is owed no
 * row where it is outside, and the rows the line is owed are the members of the class nearest it.
 */
class AValueTheDeclarationsRefuseIsNoPointOfTheBorderTest {

    private static final String MULTIPLES_OF_A_THOUSAND = """
            module p
            data T = Int
              invariant value >= 0 && %s
            behavior f : (t: T) -> Int
            let f (t) = if t <= 1950000 then 1 else 2
            """;

    @Test
    void theNumberBesideTheLineThatIsOutsideTheClassIsRefused() {
        for (String clause : List.of("Int.floorMod(value, 1000) == 0",
                "Int.floorMod(value, 1000) >= 0 && Int.floorMod(value, 1000) <= 0",
                "Int.floorMod(value, -1000) == 0")) {
            BorderAssessment line = lineAt(clause, "1950000");
            assertEquals(new ItemAssessment.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                    line.items().get(new DomainPoint.BesideTheLine(Towards.ABOVE)), clause);
            assertTrue(line.items().get(new DomainPoint.AtTheLine())
                    instanceof ItemAssessment.Owed, clause);
        }
    }

    /** The members of the class on each side of the line are rows the partitions are owed. */
    @Test
    void aPartitionIsOwedARowAtAMemberOfTheClass() {
        assertEquals(List.of("T(1949000)"), rowsAt(MULTIPLES_OF_A_THOUSAND.formatted(
                "Int.floorMod(value, 1000) == 0"), "0 <= t < 1950000"));
        assertEquals(List.of("T(1951000)"), rowsAt(MULTIPLES_OF_A_THOUSAND.formatted(
                "Int.floorMod(value, 1000) == 0"), "1950000 < t"));
    }

    /** A remainder that is left more than one number says nothing of the value's class. */
    @Test
    void aRemainderTheRulesLeaveSeveralNumbersIsNoClass() {
        BorderAssessment line = lineAt("Int.floorMod(value, 1000) <= 1", "1950000");
        assertTrue(line.items().get(new DomainPoint.BesideTheLine(Towards.ABOVE))
                instanceof ItemAssessment.Owed);
    }

    private static BorderAssessment lineAt(String clause, String value) {
        for (BorderAssessment border : linesOf(MULTIPLES_OF_A_THOUSAND.formatted(clause))) {
            if (border.value().equals(value)) {
                return border;
            }
        }
        throw new AssertionError("no line at " + value + " for " + clause);
    }

    private static List<String> rowsAt(String model, String label) {
        List<String> inputs = new ArrayList<>();
        for (BorderAssessment border : linesOf(model)) {
            for (ItemAssessment item : border.items().values()) {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    continue;
                }
                for (ItemAssessment.Attempt attempt : owed.searches().each()) {
                    if (attempt instanceof ItemAssessment.Attempt.Certified certified
                            && certified.row().purposes().stream()
                                    .anyMatch(each -> each.labels().contains(label))) {
                        inputs.add(certified.row().inputs().getFirst().text());
                    }
                }
            }
        }
        return inputs;
    }

    private static List<BorderAssessment> linesOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "p");
        assertNotNull(read, "the model under test compiles");
        List<BorderAssessment> lines = read.get("f");
        assertNotNull(lines, "f was measured");
        return lines;
    }
}
