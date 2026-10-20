package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A number made of the elements of a list is read the same whether the list is a position of the
 * input or the answer of an injected behavior. Two walks decide what keeps every element of a
 * list once — the input's, down to a position, and the answer's, down to a dependency's answer —
 * and this is what keeps them from parting: each shape is written over both, and has to come out
 * read on both or unread on both.
 */
class AListTheResponseHoldsIsReadWhereverTheSameListOfTheInputIsTest {

    private static final String OF_THE_INPUT = """
            module example.parity

            data Many
            data Few
            data Item = { sku: String, quantity: Int, active: Bool }

            behavior decide : (xs: List<Item>, ns: List<Int>) -> Many | Few

            let decide (xs, ns) =
                if <number> >= 4
                then Many else Few
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

            let decide (order, readSnap) =
                if <number> >= 4
                then Many else Few
            """;

    /** Each shape over {@code ROWS}, and whether it is read. */
    private static Map<String, Boolean> shapes() {
        Map<String, Boolean> shapes = new LinkedHashMap<>();
        shapes.put("List.length(ROWS)", true);
        shapes.put("List.length(List.sortBy(.sku, ROWS))", true);
        shapes.put("List.length(List.map(x -> x, ROWS))", true);
        shapes.put("List.fold((acc, x) -> acc + 1, 0, ROWS)", true);
        shapes.put("List.fold((acc, x) -> acc + 1, 0, List.sortBy(.sku, ROWS))", true);
        shapes.put("List.sum(List.map(.quantity, ROWS))", true);
        shapes.put("List.fold((acc, x) -> acc + x.quantity, 0, ROWS)", true);
        shapes.put("List.fold((acc, x) -> acc + x.quantity, 0, List.sortBy(.sku, ROWS))", true);
        shapes.put("List.sum(List.map(.quantity, List.sortBy(.sku, ROWS)))", true);
        shapes.put("List.sum(List.map(.quantity, List.sortBy(.sku, List.sortBy(.quantity, ROWS))))",
                true);
        shapes.put("List.sum(List.map(x -> x, List.map(.quantity, ROWS)))", true);
        shapes.put("List.sum(List.sortBy(x -> x, List.map(.quantity, ROWS)))", true);
        shapes.put("List.sum(List.map(.quantity, List.map(x -> x, ROWS)))", true);
        shapes.put("List.sum(List.map(.quantity, List.sortBy(.sku, List.map(x -> x, ROWS))))",
                true);
        shapes.put("List.sum(List.map(.quantity, List.map(x -> x, List.sortBy(.sku, ROWS))))",
                true);
        shapes.put("List.sum(List.map(.quantity, List.sortBy(.quantity, List.map(x -> x, ROWS))))",
                true);
        // What keeps some of the elements is a sum over those and over no element of the list.
        shapes.put("List.sum(List.map(.quantity, List.filter(i -> i.active, ROWS)))", false);
        shapes.put("List.fold((acc, x) -> acc + x.quantity, 0, List.filter(i -> i.active, ROWS))",
                false);
        // Neither side reads a sum over what a closure puts end to end, a fold over a map, or a
        // reordering of the numbers a fold adds.
        shapes.put("List.sum(List.flatMap(i -> [i.quantity], ROWS))", false);
        shapes.put("List.fold((acc, x) -> acc + x, 0, List.map(.quantity, ROWS))", false);
        shapes.put("List.fold((acc, x) -> acc + x, 0,"
                + " List.sortBy(x -> x, List.map(.quantity, ROWS)))", false);
        // A total taken directly of a list in another order is the total of the list, and one of
        // a list that kept some of the elements is not.
        shapes.put("List.sum(NUMS)", true);
        shapes.put("List.sum(List.reverse(NUMS))", true);
        shapes.put("List.sum(List.sortBy(x -> x, NUMS))", true);
        shapes.put("List.sum(List.take(2, NUMS))", false);
        shapes.put("List.sum(List.reverse(List.filter(x -> x > 0, NUMS)))", false);
        return shapes;
    }

    private static String reportOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(), () -> "the source compiles: " + model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void everyShapeIsReadOnBothSidesOrOnNeither() {
        assertFalse(shapes().isEmpty());
        shapes().forEach((shape, read) -> {
            String ofTheInput = reportOf(
                    OF_THE_INPUT.replace("<number>",
                            shape.replace("ROWS", "xs").replace("NUMS", "ns")));
            assertEquals(read, !ofTheInput.contains("not read: comparison"),
                    () -> "over the input: " + shape + "\n" + ofTheInput);
            String ofTheResponse = reportOf(OF_THE_RESPONSE.replace("<number>",
                    shape.replace("ROWS", "readSnap(order).rows")
                            .replace("NUMS", "readSnap(order).ns")));
            assertEquals(read, !ofTheResponse.contains("not read: comparison"),
                    () -> "over the response: " + shape + "\n" + ofTheResponse);
        });
    }
}
