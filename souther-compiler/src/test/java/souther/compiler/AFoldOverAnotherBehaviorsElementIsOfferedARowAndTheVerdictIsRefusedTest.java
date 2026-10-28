package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body no row of its own tells from one answering a constant, where the rows that would are of
 * another behavior's elements, is offered the row that does and is not satisfied until it is
 * written down — end to end, from what the search found to what a build is told and what
 * {@code --generate} writes.
 */
class AFoldOverAnotherBehaviorsElementIsOfferedARowAndTheVerdictIsRefusedTest {

    private static final String MODEL = """
            module repro.open

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Throw = List<Pin>
                invariant List.allDistinctBy(p -> p, value)

            behavior points : (t: Throw) -> Int

            let points (t) = {
                let n = List.length(t.value)
                if n == 1 then List.sum(List.map(p -> p.value, t.value)) else n
            }

            example points
                | (Throw([])) -> 0
                | (Throw([Pin(12)])) -> 12
                | (Throw([Pin(1), Pin(2)])) -> 2
                | (Throw([Pin(1), Pin(2), Pin(3)])) -> 3

            behavior score : (throws: List<Throw>) -> Int

            let score (throws) = %s

            example score
                | ([]) -> 0
            """;

    private static final String WRONG = "List.length(throws) * 100";

    private static final String RIGHT = "List.fold((acc, t) -> acc + points(t), 0, throws)";

    @Test
    void theVerdictIsNotSatisfiedWhileTheRewriteIsNotToldApart() {
        for (String body : List.of(WRONG, RIGHT)) {
            Compilation compilation = compiled(MODEL.formatted(body));

            assertTrue(rewritesUnnoticed(compilation) > 0,
                    () -> "the body written as the one answer the row gave: " + body);
            assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                    AdequacyReport.of(compilation).adequacy(), body);
        }
    }

    @Test
    void generateOffersTheRowThatTellsItApart() {
        for (String body : List.of(WRONG, RIGHT)) {
            Compilation compilation = compiled(MODEL.formatted(body));

            String block = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                            OfferingRequest.overTheModule("repro.open")),
                    Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                    compilation.db()).text();

            List<RowsOfABlock.Row> offered = RowsOfABlock.of(block).stream()
                    .filter(row -> row.behavior().equals("score")).toList();
            assertEquals(1, offered.size(), () -> body + " is offered one row: " + block);
            assertTrue(offered.getFirst().written().contains("Throw("),
                    () -> "and it holds a throw: " + block);
            assertTrue(offered.getFirst().written().contains("<?>"),
                    () -> "and leaves the answer to be written: " + block);
        }
    }

    /** The row offered is one the body answers otherwise than the constant on: stated as that
     *  constant, it fails. */
    @Test
    void theRowOfferedIsOneTheBodyDoesNotAnswerTheConstantOn() {
        for (String body : List.of(WRONG, RIGHT)) {
            Compilation compilation = compiled(MODEL.formatted(body));
            String block = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                            OfferingRequest.overTheModule("repro.open")),
                    Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                    compilation.db()).text();
            String offered = RowsOfABlock.of(block).stream()
                    .filter(row -> row.behavior().equals("score")).findFirst().orElseThrow()
                    .written();
            String stated = offered.replace("<?>", "0");

            Compilation statedAsTheConstant = Compilation.ofSource(
                    MODEL.formatted(body).replace("    | ([]) -> 0\n", "    | ([]) -> 0\n" + stated
                            + "\n"), "Main");
            statedAsTheConstant.measure(Adequacy.Asked.fullReport());
            statedAsTheConstant.answerEverything();

            assertEquals(List.of(DiagnosticCode.E1905.toString()),
                    statedAsTheConstant.errors().stream()
                            .map(e -> e.diagnostic().code().toString()).toList(),
                    () -> body + ": the row " + offered + " stated as 0 does not hold of the body");
        }
    }

    private static long rewritesUnnoticed(Compilation compilation) {
        return Adequacy.accountOf(compilation.db(), compilation.modules().getFirst()).stream()
                .filter(each -> each.kind() == Adequacy.Kind.REWRITE_UNNOTICED)
                .count();
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
