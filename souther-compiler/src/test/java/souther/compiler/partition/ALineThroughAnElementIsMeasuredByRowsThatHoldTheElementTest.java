package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.ObservedValue;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line through an element a walk hands its step, where the container is made of the input, is
 * measured by rows whose container holds that element: a row with nothing to walk never gets to
 * the comparison, whatever it holds at the line.
 *
 * <p>Held to the rows as they ran and were read back, and not to the conditions the way carries:
 * a row composed for the line that does not hold the element shows nothing of it.
 */
class ALineThroughAnElementIsMeasuredByRowsThatHoldTheElementTest {

    /**
     * {@code a + n >= 10} over {@code List.rangeInclusive(3, days)} is at {@code a} of seven, where
     * the element is three; a row at it, beside it or either side of it makes the list hold three,
     * which is {@code days} of three or more.
     */
    @Test
    void aLineThroughAWholeNumberInTurnIsMeasuredByRowsWhoseListHoldsIt() {
        Compilation compilation = compiled("a: Int, days: Int", "List<Int>",
                "List.rangeInclusive(3, days) |> List.filter(n -> a + n >= 10)");
        assertEquals(List.of("7"), lines(compilation));
        List<ObservedInputs> rows = rowsAtEveryItem(compilation);
        assertFalse(rows.isEmpty(), "the line has its rows");
        assertRowsHold(rows, 1, value -> value instanceof ObservedValue.Integer(long days)
                && days >= 3);
    }

    /**
     * {@code a + i >= 3} over where an element of {@code xs} stands is at {@code a} of three, where
     * the element stands first; a row there holds an element. And no line is drawn where the
     * position meets the most a list holds, which is the language's end and no model's.
     */
    @Test
    void aLineThroughWhereAnElementStandsIsMeasuredByRowsThatHoldAnElement() {
        Compilation compilation = compiled("a: Int, xs: List<Int>", "List<Bool>",
                "List.mapIndexed((i, _) -> a + i >= 3, xs)");
        assertEquals(List.of("3"), lines(compilation));
        List<ObservedInputs> rows = rowsAtEveryItem(compilation);
        assertFalse(rows.isEmpty(), "the line has its rows");
        assertRowsHold(rows, 1, value -> value instanceof ObservedValue.Sequence(var elements)
                && !elements.isEmpty());
    }

    private static void assertRowsHold(List<ObservedInputs> rows, int parameter,
                                       Predicate<ObservedValue> holding) {
        for (ObservedInputs row : rows) {
            assertTrue(holding.test(row.inputs().get(parameter)), row::toString);
        }
    }

    /** The rows read back at every item owed of every line of {@code m}, every item owed having
     *  some. */
    private static List<ObservedInputs> rowsAtEveryItem(Compilation compilation) {
        List<ObservedInputs> rows = new ArrayList<>();
        for (BorderAssessment line : measured(compilation)) {
            line.items().forEach((point, item) -> {
                if (!(item instanceof ItemAssessment.Owed owed)) {
                    return;
                }
                List<ObservedInputs> here = owed.searches().each().stream()
                        .filter(ItemAssessment.Attempt.Certified.class::isInstance)
                        .map(ItemAssessment.Attempt.Certified.class::cast)
                        .map(ItemAssessment.Attempt.Certified::readBack).toList();
                assertFalse(here.isEmpty(), () -> point + " has a row: " + owed);
                rows.addAll(here);
            });
        }
        return rows;
    }

    private static List<String> lines(Compilation compilation) {
        return measured(compilation).stream().map(BorderAssessment::value).toList();
    }

    private static List<BorderAssessment> measured(Compilation compilation) {
        List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "w1").get("m");
        assertNotNull(lines, "m was measured");
        return lines;
    }

    private static Compilation compiled(String parameters, String answer, String body) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                behavior m : (%s) -> %s
                let m (%s) = %s
                """.formatted(parameters, answer, parameters.replaceAll(":\\s*[A-Za-z<>]+", ""),
                body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return compilation;
    }
}
