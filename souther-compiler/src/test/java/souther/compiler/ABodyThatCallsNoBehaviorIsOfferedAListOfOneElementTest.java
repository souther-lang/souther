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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body over a list of plain values that calls no behavior has no row of a callee to start the
 * list's elements from. What stands for the element's type is what they start from, so the row
 * that tells the body from one answering a constant is still offered, and one no list tells from
 * the constant is not given a row.
 */
class ABodyThatCallsNoBehaviorIsOfferedAListOfOneElementTest {

    private static final String MODEL = """
            module repro.nocallee

            behavior f : (xs: List<Int>) -> %s

            let f (xs) = %s

            example f
                | ([]) -> %s
            """;

    private static final List<String[]> BODIES = List.of(
            new String[] {"List<Int>", "List.map(x -> x + x + 1, xs)", "[]"},
            new String[] {"Int", "List.fold((acc, x) -> acc + x, 0, xs)", "0"});

    @Test
    void generateOffersARowHoldingAnElement() {
        for (String[] body : BODIES) {
            Compilation compilation = compiled(body);

            String block = offered(compilation);

            List<RowsOfABlock.Row> rows = rowsForTheRewrite(block);
            assertEquals(1, rows.size(), () -> body[1] + " is offered one row: " + block);
            assertTrue(rows.getFirst().written().contains("<?>"),
                    () -> body[1] + " leaves the answer to be written: " + block);
            assertTrue(!rows.getFirst().written().contains("([]) ->"),
                    () -> body[1] + " holds an element: " + block);
        }
    }

    @Test
    void theVerdictIsNotSatisfiedWhileTheRewriteIsNotToldApart() {
        for (String[] body : BODIES) {
            Compilation compilation = compiled(body);

            assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                    AdequacyReport.of(compilation).adequacy(), body[1]);
        }
    }

    @Test
    void aBodyNoListTellsFromTheConstantIsOfferedNoRow() {
        Compilation compilation = compiled(new String[] {"List<Int>", "[]", "[]"});

        assertEquals(List.of(), rowsForTheRewrite(offered(compilation)));
    }

    private static String offered(Compilation compilation) {
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("repro.nocallee")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }

    private static List<RowsOfABlock.Row> rowsForTheRewrite(String block) {
        return RowsOfABlock.of(block).stream()
                .filter(row -> row.behavior().equals("f"))
                .filter(row -> row.name().filter(name ->
                        name.startsWith("the body answering what f")).isPresent())
                .toList();
    }

    private static Compilation compiled(String[] body) {
        Compilation compilation = Compilation.ofSource(
                MODEL.formatted(body[0], body[1], body[2]), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
