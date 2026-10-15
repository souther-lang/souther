package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Every note under a block of generated rows names what it is about.
 *
 * <p>An arm whose way in this reading places at no class comes to nothing before anything is
 * composed, so there is no combination it is a fact about. Said in the words a combination's note
 * is said in, it named the combination it did not have — an empty name — and stayed there after a
 * row composed for a class went through the arm.
 */
class EveryNoteOfTheBlockNamesWhatItIsAboutTest {

    /** A body whose arms are reached through two guards, and one written row through neither. */
    private static final String MODEL = """
            module probe.notes

            data Line = { price: Int }
                invariant price >= 1 && price <= 100

            data Order = { lines: List<Line>, coupon: Int }
                invariant coupon >= 0 && coupon <= 50

            data Nothing
            data Discounted = { total: Int }
            data Full = { total: Int }

            behavior bill : (order: Order) -> Nothing | Discounted | Full
            let bill (order) =
                if List.length(order.lines) == 0 then Nothing
                else if order.coupon >= 10 then Discounted { total = 1 }
                else Full { total = 1 }

            example bill
                | "full" : (Order { lines = [ Line { price = 5 } ], coupon = 0 }) -> Full { total = 1 }
            """;

    @Test
    void noNoteIsSaidOfNothing() {
        String block = block();
        assertFalse(block.isBlank(), "the model leaves something for a block to offer");
        assertEquals(List.of(), block.lines().filter(line -> line.startsWith("//")
                && line.contains("``")).toList(), "a note names what it is about");
    }

    private static String block() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String module = compilation.modules().getFirst();
        Map<String, Adequacy.Filling> generated = Adequacy.generatedOf(compilation.db(), module);
        assertNotNull(generated, "the model under test compiles");
        return GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule(module)),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .text();
    }
}
