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
 * A number made of the elements of a list is read the same whether the list is a position of the
 * input or the answer of an injected behavior, and as the same number however it is spelled. Two
 * walks decide what keeps every element of a list once — the input's, down to a position, and the
 * answer's, down to a dependency's answer — and this is what keeps them from parting: each shape is
 * written over both, and has to come out read on both or unread on both.
 *
 * <p>Read is not enough. Spellings of one number — a count and a fold adding one, a total of a list
 * and of the list reversed — are one term, so on each side every spelling in a group comes out with
 * the report the first one does. A spelling read as a term of its own would put a second line on
 * one number, and a row composed for one would be offered at the other.
 */
class AListTheResponseHoldsIsReadWhereverTheSameListOfTheInputIsTest {

    private static final String OF_THE_INPUT = """
            module example.parity

            data Many
            data Few
            data Item = { sku: String, quantity: Int, active: Bool }

            behavior decide : (xs: List<Item>, ns: List<Int>) -> Many | Few

            let decide (xs, ns) = {
                <bound>
                if <number> >= 4
                then Many else Few
            }
            """;

    private static final String OF_THE_RESPONSE = """
            module example.parity

            data Many
            data Few
            data Item = { sku: String, quantity: Int, active: Bool }
            data Cart = { items: List<Item> }
            data Snap = { rows: List<Item>, ns: List<Int> }
            behavior readSnap : (order: Cart) -> Snap
                constructs Snap
            behavior decide : (order: Cart) -> Many | Few
                depends on readSnap

            let decide (order, readSnap) = {
                <bound>
                if <number> >= 4
                then Many else Few
            }
            """;

    /** Spellings of one number over {@code ROWS} or {@code NUMS}, each read as the first is. */
    private static List<List<String>> readAsOne() {
        return List.of(
                List.of("List.length(ROWS)",
                        "List.length(List.sortBy(.sku, ROWS))",
                        "List.length(List.map(x -> x, ROWS))",
                        "List.fold((acc, x) -> acc + 1, 0, ROWS)",
                        "List.fold((acc, x) -> acc + 1, 0, List.sortBy(.sku, ROWS))"),
                List.of("List.sum(List.map(.quantity, ROWS))",
                        "List.fold((acc, x) -> acc + x.quantity, 0, ROWS)",
                        "List.fold((acc, x) -> acc + x.quantity, 0, List.sortBy(.sku, ROWS))",
                        "List.sum(List.map(.quantity, List.sortBy(.sku, ROWS)))",
                        "List.sum(List.map(.quantity, List.sortBy(.sku, List.sortBy(.quantity, ROWS))))",
                        "List.sum(List.map(x -> x, List.map(.quantity, ROWS)))",
                        "List.sum(List.sortBy(x -> x, List.map(.quantity, ROWS)))",
                        "List.sum(List.map(.quantity, List.map(x -> x, ROWS)))",
                        "List.sum(List.map(.quantity, List.sortBy(.sku, List.map(x -> x, ROWS))))",
                        "List.sum(List.map(.quantity, List.map(x -> x, List.sortBy(.sku, ROWS))))",
                        "List.sum(List.map(.quantity, List.sortBy(.quantity, List.map(x -> x, ROWS))))"),
                // A total taken directly of a list in another order is the total of the list.
                List.of("List.sum(NUMS)",
                        "List.sum(List.reverse(NUMS))",
                        "List.sum(List.sortBy(x -> x, NUMS))",
                        "List.sum(List.reverse(List.sortBy(x -> x, NUMS)))",
                        "List.sum(List.map(x -> x, List.reverse(NUMS)))",
                        "List.sum(ys)"),
                // And a total of what each element comes to is the same over the list reversed.
                List.of("List.sum(List.map(x -> 2 * x, NUMS))",
                        "List.sum(List.map(x -> 2 * x, List.reverse(NUMS)))"));
    }

    /**
     * Shapes neither side reads. What keeps some of the elements is a sum over those and over no
     * element of the list: {@code [4, 6]} reversed and taken one of comes to six where both come to
     * ten. Nor is a sum over what a closure puts end to end, a fold over a map, or a reordering of
     * the numbers a fold adds read.
     */
    private static List<String> unread() {
        return List.of(
                "List.sum(List.map(.quantity, List.filter(i -> i.active, ROWS)))",
                "List.fold((acc, x) -> acc + x.quantity, 0, List.filter(i -> i.active, ROWS))",
                "List.sum(List.take(1, List.reverse(NUMS)))",
                "List.sum(List.reverse(List.filter(x -> x > 0, NUMS)))",
                "List.sum(List.flatMap(i -> [i.quantity], ROWS))",
                "List.fold((acc, x) -> acc + x, 0, List.map(.quantity, ROWS))",
                "List.fold((acc, x) -> acc + x, 0,"
                        + " List.sortBy(x -> x, List.map(.quantity, ROWS)))");
    }

    private static String overTheInput(String shape) {
        return reportOf(OF_THE_INPUT, shape, "xs", "ns");
    }

    private static String overTheResponse(String shape) {
        return reportOf(OF_THE_RESPONSE, shape, "readSnap(order).rows", "readSnap(order).ns");
    }

    /**
     * The report of {@code shape} compared in {@code template}, with where each part stands left
     * out: spellings of one number differ in length, and what is compared is what was read.
     * {@code ys} is {@code NUMS} reversed and bound to a name.
     */
    private static String reportOf(String template, String shape, String rows, String nums) {
        String bound = shape.contains("ys") ? "let ys = List.reverse(" + nums + ")" : "";
        String model = template.replace("<bound>", bound).replace("<number>",
                shape.replace("ROWS", rows).replace("NUMS", nums));
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(), () -> "the source compiles: " + model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()))
                .replaceAll("\\d+:\\d+", "");
    }

    @Test
    void everySpellingOfANumberIsReadAsTheFirstOnBothSides() {
        assertFalse(readAsOne().isEmpty());
        for (List<String> spellings : readAsOne()) {
            String input = overTheInput(spellings.getFirst());
            String response = overTheResponse(spellings.getFirst());
            assertFalse(input.contains("not read: comparison"), input);
            assertFalse(response.contains("not read: comparison"), response);
            for (String each : spellings.subList(1, spellings.size())) {
                assertEquals(input, overTheInput(each), "over the input: " + each);
                assertEquals(response, overTheResponse(each), "over the response: " + each);
            }
        }
    }

    @Test
    void whatNeitherSideReadsIsUnreadOnBoth() {
        for (String shape : unread()) {
            String input = overTheInput(shape);
            assertTrue(input.contains("not read: comparison"), "over the input: " + shape + "\n"
                    + input);
            String response = overTheResponse(shape);
            assertTrue(response.contains("not read: comparison"), "over the response: " + shape
                    + "\n" + response);
        }
    }
}
