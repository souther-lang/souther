package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Citation;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.ConditionReportAnchor;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.OnTheWay;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A condition a reading places itself is placed where that reading met it, and not where another
 * reading of the same body met its condition of the same number.
 *
 * <p>A body is read for what divides its positions and for which ways it decides, and each reading
 * numbers the conditions it meets in the order it meets them. The two orders differ: in this model
 * the first condition the decision met is not the first the division did. A place looked up by
 * number in the other reading's places is some other condition's place, or none.
 */
class AConditionIsPlacedByTheReadingThatNamedItTest {

    /**
     * A body whose conditions are truths a reading places itself, read through a helper and
     * outside it, so the two readings meet them in different orders.
     */
    private static final String MODEL = """
            module example.truth

            behavior g : (a: Int, ok: Bool, big: Bool) -> Int

            let check (b: Bool, n: Int): Bool = b && n > 2

            let g (a, ok, big) =
                if check(ok, a) then 1
                else if big || a == 7 then 2
                else if check(big, a + 1) then 3
                else 4

            example g
                | "one" : (5, true, false) -> 1
            """;

    @Test
    void aConditionOfTheDecisionIsPlacedWhereTheDecisionMetIt() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        DecisionReading read = compilation.db().ask(new Adequacy.Decides("example.truth"))
                .value().get("g").read();
        Map<ConditionOccurrence, Citation> divided = compilation.db()
                .ask(new Adequacy.ConditionsMet("example.truth", "g")).value();

        int asked = 0;
        boolean anotherReadingWouldDiffer = false;
        for (DecisionReading.Ruled way : read.found()) {
            for (OnTheWay each : way.states().onTheWay()) {
                if (!(each.anchor() instanceof ConditionReportAnchor.WhereTheReadingMetIt(
                        var _, var condition))) {
                    continue;
                }
                asked++;
                assertEquals(read.metAt().get(condition),
                        Sites.placeIfKnown(compilation.db(), each.anchor()),
                        () -> condition + " is placed where the decision met it");
                // The same number among the other reading's places, which is what a lookup that
                // did not ask which reading named the condition would have come back with.
                anotherReadingWouldDiffer |= divided.entrySet().stream()
                        .filter(other -> other.getKey().ordinal() == condition.ordinal())
                        .anyMatch(other -> !other.getValue().equals(
                                read.metAt().get(condition)));
            }
        }
        assertTrue(asked > 0, "the decision's ways carry conditions it places itself");
        assertTrue(anotherReadingWouldDiffer, "and the other reading numbers some of them"
                + " differently, which is what makes asking the right one the question");
        assertNotEquals(Map.of(), divided, "the division places conditions of its own too");
    }
}
