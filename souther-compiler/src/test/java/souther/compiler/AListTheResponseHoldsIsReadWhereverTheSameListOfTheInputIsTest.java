package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total of what takes and drops keep of a list is read the same whether the list is a position
 * of the input or the answer of an injected behavior, and as the same number however the takes
 * and drops are stacked. Both sides read the stack as one selection of positions, from the
 * furthest drop to the nearest take; over the answer the elements are then asked of the answer in
 * the order it hands them, over the input of the position.
 */
class AListTheResponseHoldsIsReadWhereverTheSameListOfTheInputIsTest {

    private static final String OF_THE_INPUT = """
            module example.parity

            data Many
            data Few

            behavior decide : (ns: List<Int>) -> Many | Few

            let decide (ns) =
                if <number> >= 4
                then Many else Few
            """;

    private static final String OF_THE_RESPONSE = """
            module example.parity

            data Many
            data Few
            data Cart = { items: List<Int> }
            data Snap = { ns: List<Int> }
            behavior readSnap : (order: Cart) -> Snap
                constructs Snap
            behavior decide : (order: Cart) -> Many | Few
                depends on readSnap

            let decide (order, readSnap) =
                if <number> >= 4
                then Many else Few
            """;

    /**
     * Spellings of one number over {@code NUMS}, each read as the first is: a selection that keeps
     * nothing, whichever order its cuts are written in, and one that keeps the second to the
     * fourth, through a drop inside a take or outside it, and through two takes of which the
     * nearer decides.
     */
    private static List<List<String>> readAsOne() {
        return List.of(
                List.of("List.sum(List.take(0, NUMS))",
                        "List.sum(List.drop(3, List.take(3, NUMS)))"),
                List.of("List.sum(List.take(3, List.drop(1, NUMS)))",
                        "List.sum(List.drop(1, List.take(4, NUMS)))",
                        "List.sum(List.take(5, List.take(3, List.drop(1, NUMS))))"));
    }

    private static String overTheInput(String shape) {
        return reportOf(OF_THE_INPUT, shape, "ns");
    }

    private static String overTheResponse(String shape) {
        return reportOf(OF_THE_RESPONSE, shape, "readSnap(order).ns");
    }

    /**
     * The report of {@code shape} compared in {@code template}, with where each part stands left
     * out: spellings of one number differ in length, and what is compared is what was read.
     */
    private static String reportOf(String template, String shape, String nums) {
        Compilation compilation = Compilation.ofSource(
                template.replace("<number>", shape.replace("NUMS", nums)), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("\\d+:\\d+", "");
    }

    /** Each spelling is read, and read as the first of its group is, on each side. */
    @Test
    void everySpellingOfANumberIsReadAsTheFirstOnBothSides() {
        for (List<String> spellings : readAsOne()) {
            String input = overTheInput(spellings.getFirst());
            String response = overTheResponse(spellings.getFirst());
            assertFalse(UnreadBesideItsStops.in(input), input);
            assertFalse(UnreadBesideItsStops.in(response), response);
            for (String each : spellings.subList(1, spellings.size())) {
                assertEquals(input, overTheInput(each), "over the input: " + each);
                assertEquals(response, overTheResponse(each), "over the response: " + each);
            }
        }
    }

    /**
     * A reversal between two cuts puts the positions the outer one counts in another list, so the
     * stack is no selection of the list under it, and it is unread on both sides.
     */
    @Test
    void aReversalBetweenTwoCutsIsUnreadOnBoth() {
        String shape = "List.sum(List.take(1, List.reverse(List.drop(1, NUMS))))";
        String input = overTheInput(shape);
        String response = overTheResponse(shape);
        assertTrue(UnreadBesideItsStops.in(input), input);
        assertTrue(UnreadBesideItsStops.in(response), response);
    }
}
