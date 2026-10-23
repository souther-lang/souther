package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk that stops at an element, over a list a helper chooses between a list of the input and
 * none, stops at an element of the input's list, and only where the helper chose it.
 *
 * <p>{@code if c.open then c.items else []} holds the elements of {@code c.items} in their order
 * where the cart is open and nothing where it is closed. So a row at a line inside
 * {@code List.all} over it is read at the element the walk stopped at, and is a row at the line
 * only where the cart is open: a closed cart holding the same element never gets to the comparison.
 */
class AnElementAWalkStopsAtIsOneOfTheListAHelperChoseTest {

    private static final String MODEL = """
            module p
            data LI = { quantity: Int, unitPrice: Int }
            data Cart = { open: Bool, items: List<LI> }
            data Invalid = { n: Int }
            let act (c: Cart) = if c.open then c.items else []
            behavior f : (c: Cart) -> Int | Invalid
            let f (c) = {
                guard List.length(act(c)) >= 1 else Invalid { n = 1 }
                guard List.all(i -> i.quantity >= 1, act(c)) else Invalid { n = 0 }
                1
            }
            """;

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Every point of both lines is offered a row, and each row holds an open cart. */
    @Test
    void everyPointIsOfferedARowOfAnOpenCart() {
        Compilation compilation = measured(MODEL);
        Generator.GenerationResult offered = OfferedAtTheLines.of(compilation, "p", "f");

        assertEquals(List.of(), offered.unresolved(), () -> report(compilation));
        List<String> atTheElements = offered.rows().stream()
                .filter(row -> labelOf(row).contains("c.items[*].quantity"))
                .map(row -> row.inputs().getFirst().text()).toList();
        assertEquals(4, atTheElements.size(), () -> report(compilation));
        atTheElements.forEach(text -> assertTrue(text.contains("open = true"), text));
    }

    /**
     * A row of a closed cart is no row at the line, whatever its element holds; the same element
     * in an open cart is. Over a list the helper chose nothing for, the walk answers without
     * stopping anywhere, so the closed cart passes the guard as the open one does and only the
     * cart being closed keeps it from the comparison. The control is the open one: it meets the
     * point.
     */
    @Test
    void aClosedCartHoldingTheElementIsNoRowAtTheLine() {
        String model = """
                module p
                data LI = { quantity: Int, unitPrice: Int }
                data Cart = { open: Bool, items: List<LI> }
                data Invalid = { n: Int }
                let act (c: Cart) = if c.open then c.items else []
                behavior f : (c: Cart) -> Int | Invalid
                let f (c) = {
                    guard List.all(i -> i.quantity >= 1, act(c)) else Invalid { n = 0 }
                    1
                }
                """;
        String open = report(measured(model + """

                example f
                    | "open" : (Cart { open = true, items = [LI { quantity = 1, unitPrice = 0 }] }) -> 1
                """));
        String closed = report(measured(model + """

                example f
                    | "closed" : (Cart { open = false, items = [LI { quantity = 1, unitPrice = 0 }] }) -> 1
                """));

        assertTrue(onPointOfTheElements(closed), closed);
        assertFalse(onPointOfTheElements(open), open);
    }

    /**
     * Where the cart is closed the helper chooses nothing, so a walk over what it chose there
     * applies its closure to nothing and the comparison in it is reached by no row: no line is
     * drawn there to owe a row. The control is the same walk where the cart is open.
     */
    @Test
    void aWalkOverWhatTheHelperChoseForAClosedCartComparesNothing() {
        String closed = report(measured("""
                module p
                data LI = { quantity: Int, unitPrice: Int }
                data Cart = { open: Bool, items: List<LI> }
                let act (c: Cart) = if c.open then c.items else []
                behavior f : (c: Cart) -> Int
                let f (c) = if c.open then 0
                    else (if List.all(i -> i.quantity >= 1, act(c)) then 1 else 2)
                """));
        String open = report(measured("""
                module p
                data LI = { quantity: Int, unitPrice: Int }
                data Cart = { open: Bool, items: List<LI> }
                let act (c: Cart) = if c.open then c.items else []
                behavior f : (c: Cart) -> Int
                let f (c) = if c.open
                    then (if List.all(i -> i.quantity >= 1, act(c)) then 1 else 2) else 0
                """));

        assertTrue(closed.contains("border      not applicable"), closed);
        assertTrue(open.contains("border      borders 1   obligations 0/4"), open);
    }

    /** Whether {@code report} still owes the point on the line of the elements at one. */
    private static boolean onPointOfTheElements(String report) {
        List<String> lines = report.lines().toList();
        for (int at = 0; at + 1 < lines.size(); at++) {
            if (lines.get(at).contains("at the ON point")
                    && lines.get(at + 1).contains("c.items[*].quantity: = 1")) {
                return true;
            }
        }
        return false;
    }

    private static String labelOf(Generator.GeneratedRow row) {
        return row.purposes().stream()
                .filter(Generator.Purpose.ForAPoint.class::isInstance)
                .map(each -> ((Generator.Purpose.ForAPoint) each).label())
                .findFirst().orElse("");
    }
}
