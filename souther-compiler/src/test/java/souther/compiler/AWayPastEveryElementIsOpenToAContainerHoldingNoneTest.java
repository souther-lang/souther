package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The way past every element meeting a condition is open to a container holding none.
 *
 * <p>Every element of an empty list meets anything, so where the rules leave an element no value
 * the condition holds of, the way is still taken — by the list holding nothing. Read as a relation
 * of the element, the condition narrowed the region to nothing there, and the rules past it were
 * said to be owed no row.
 */
class AWayPastEveryElementIsOpenToAContainerHoldingNoneTest {

    /** `n > 0` is a value no `Item` holds, so only the empty list takes `all` the true way. */
    private static final String MODEL = """
            module probe.vacuous

            data Item = { n: Int }
                invariant n >= -5 && n <= 0

            data Input = { items: List<Item>, gate: Int }
                invariant gate >= -10 && gate <= 10

            data A
            data B
            data C

            behavior decide : (x: Input) -> A | B | C
            let decide (x) =
                if List.all(i -> i.n > 0, x.items) then
                    if x.gate > 0 then A else B
                else C

            example decide
                | "c" : (Input { items = [ Item { n = 0 } ], gate = 0 }) -> C
            """;

    @Test
    void theRulesPastAnEmptyListAreOwedARow() {
        Compilation compilation = measured();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertFalse(report.contains("the rules leave no value at a rule of the decision"),
                () -> "a way an empty list takes is not one the rules close:\n" + report);
    }

    @Test
    void aRowPastTheConditionHoldsNoElement() {
        Compilation compilation = measured();
        String module = compilation.modules().getFirst();
        String block = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule(module)),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();
        List<String> past = block.lines()
                .filter(line -> line.contains("items = []") && line.contains("gate = "))
                .toList();
        assertTrue(past.stream().anyMatch(line -> !line.contains("gate = 0 ")
                        && !line.contains("gate = -")),
                () -> "a row through `gate > 0` past the condition, with no element:\n" + block);
    }

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return compilation;
    }
}
