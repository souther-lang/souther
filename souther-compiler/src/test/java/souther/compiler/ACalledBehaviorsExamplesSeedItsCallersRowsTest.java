package souther.compiler;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule given its own behavior and rows is offered to its caller the way the same rule written
 * as a helper is: as the inputs its rows give.
 */
class ACalledBehaviorsExamplesSeedItsCallersRowsTest {

    private static final String PREFIX = """
            module repro.split

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Throw = List<Pin>
                invariant List.allDistinctBy(p -> p, value)

            """;

    private static final String BODY = """
            let points (t) = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            """;

    private static final String SCORE = """
            behavior score : (throws: List<Throw>) -> Int

            let score (throws) = List.fold((acc, t) -> acc + points(t), 0, throws)
            """;

    private static final String AS_BEHAVIOR = PREFIX + """
            behavior points : (t: Throw) -> Int

            """ + BODY + """
            example points
                | (Throw([])) -> 0
                | (Throw([Pin(12)])) -> 12
                | (Throw([Pin(1), Pin(2)])) -> 2
                | (Throw([Pin(1), Pin(2), Pin(3)])) -> 3

            """ + SCORE;

    private static final String AS_HELPER = PREFIX + """
            let points (t: Throw): Int = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            """ + SCORE;

    @Test
    void theRowsOfACalledBehaviorAreInputsOfItsCaller() {
        List<String> offered = offeredForScore(AS_BEHAVIOR);
        for (String throwText : List.of("Throw([])", "Throw([Pin(12)])",
                "Throw([Pin(1), Pin(2)])", "Throw([Pin(1), Pin(2), Pin(3)])")) {
            assertTrue(offered.contains("[" + throwText + "]"),
                    () -> "a list holding " + throwText + " is offered: " + offered);
        }
    }

    @Test
    void aHelperIsOfferedTheSameInputs() {
        List<String> offered = offeredForScore(AS_HELPER);
        assertTrue(offered.contains("[Throw([Pin(12)])]"), () -> "offered: " + offered);
    }

    @Test
    void aCalleeWithNoRowsSeedsNothing() {
        String withoutRows = PREFIX + """
                behavior points : (t: Throw) -> Int

                """ + BODY + SCORE;
        assertEquals(List.of("[]"), offeredForScore(withoutRows));
    }

    @Test
    void theRowsOfTheCalleeAddNoObligationToTheCaller() {
        String oneRow = PREFIX + """
                behavior points : (t: Throw) -> Int

                """ + BODY + """
                example points
                    | (Throw([Pin(12)])) -> 12

                """ + SCORE;
        assertEquals(gapsAboutScore(oneRow), gapsAboutScore(AS_BEHAVIOR),
                "what score is owed does not depend on how many rows points has");
    }

    @Test
    void theSameRowsAreOfferedInTheSameOrderEachTime() {
        assertEquals(offeredForScore(AS_BEHAVIOR), offeredForScore(AS_BEHAVIOR));
    }

    private static List<String> gapsAboutScore(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).adequacyGaps().stream()
                // The rules of score's own body. A line a declaration draws is met by whichever
                // rows reach its edges, and rows of points do.
                .filter(each -> each.kind() == Adequacy.Kind.DECISION_RULE_UNCOVERED
                        && each.about().toString().contains("behavior=score"))
                .map(each -> each.kind() + " " + each.about().getClass().getSimpleName())
                .toList();
    }

    private static List<String> offeredForScore(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("repro.split"))
                .rowsByBehavior().getOrDefault("score", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }
}
