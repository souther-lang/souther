package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many elements a count keeps is what is kept whatever a row chooses and what each decision
 * keeps, and the ways a comparison of it comes out are read from that. Read from the decisions
 * alone, the region of a guard is narrower than the rows that take it, and a combination the body
 * has a path to is not asked for.
 */
class ACountOfWhatIsKeptIsReadWithWhatIsKeptWhateverARowChoosesTest {

    /**
     * One element kept whatever a row chooses moves the threshold of the guard and no combination:
     * with it, two kept of three is one kept of the other two. Counted as the two decisions alone,
     * the guard would hold only where both are kept, and the combinations of the sum under it where
     * only one is would not be asked for.
     */
    @Test
    void anElementKeptWhateverARowChoosesMovesTheThresholdAndNoCombination() {
        String body = """
                data W = { a: Int, b: Int }

                behavior total : (w: W) -> Int
                let total (w) = {
                    let ok = List.filter(d -> d >= 17, %s)
                    guard List.length(ok) >= %d else 0 - 1
                    List.sum(ok)
                }

                example total
                    | (W { a = 20, b = 20 }) -> %d
                    | (W { a = 20, b = 1 }) -> %d
                    | (W { a = 1, b = 20 }) -> %d
                    | (W { a = 1, b = 1 }) -> %d
                """;
        int alone = behaviorOf("module example.alone\n" + body.formatted(
                "[ w.a, w.b ]", 1, 40, 20, 20, -1)).evidence().interaction().counted();
        int withOneFixed = behaviorOf("module example.fixedbase\n" + body.formatted(
                "[ 20, w.a, w.b ]", 2, 60, 40, 40, -1)).evidence().interaction().counted();

        assertEquals(7, alone, "the count of the guard's elements and the sum under it where it holds");
        assertEquals(alone, withOneFixed,
                "the same combinations whether the element kept whatever a row chooses is written");
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
    }
}
