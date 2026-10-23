package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Elements that differ, chosen for how many of them meet a statement, are chosen for a list that is
 * a field of a parameter as they are for one that is the parameter.
 *
 * <p>Past {@code List.all(i -> i.quantity >= 1, ...)} failing, a row at the line of
 * {@code List.filter(i -> i.quantity < 1, ...)} where it keeps nothing holds an element of quantity
 * one beside one under one: no element written alike is both. And past it holding, a row at the
 * line of {@code List.any(i -> i.unitPrice >= 100000, ...)} holds an element at the unit price
 * whose quantity the guard keeps. The elements are chosen by what each answers in a row holding the
 * list alone, and a list inside a parameter is held alone the way the element alone is, read where
 * it stands.
 */
class ElementsChosenForACountAreChosenInAListInsideAParameterTest {

    private static final String INSIDE = """
            module p
            data LI = { quantity: Int, unitPrice: Int }
            data Cart = { items: List<LI> }
            data Invalid = { n: Int }
            behavior f : (c: Cart) -> Int | Invalid
            let f (c) = {
                guard List.all(i -> i.quantity >= 1, c.items)
                    else Invalid { n = List.length(List.filter(i -> i.quantity < 1, c.items)) }
                1
            }
            """;

    /** The control: the same list as the parameter itself. */
    private static final String THE_PARAMETER = """
            module p
            data LI = { quantity: Int, unitPrice: Int }
            data Invalid = { n: Int }
            behavior f : (items: List<LI>) -> Int | Invalid
            let f (items) = {
                guard List.all(i -> i.quantity >= 1, items)
                    else Invalid { n = List.length(List.filter(i -> i.quantity < 1, items)) }
                1
            }
            """;

    /** Past every element holding a quantity of one or more, a line about the unit price of
     *  some element: the elements are chosen for the guard's count and the line's together. */
    private static final String PRICED_INSIDE = """
            module p
            data LI = { quantity: Int, unitPrice: Int }
            data Cart = { items: List<LI> }
            data Invalid = { n: Int }
            behavior f : (c: Cart) -> Bool | Invalid
            let f (c) = {
                guard List.all(i -> i.quantity >= 1, c.items) else Invalid { n = 1 }
                List.any(i -> i.unitPrice >= 100000, c.items)
            }
            """;

    /** The control: the same list as the parameter itself. */
    private static final String PRICED_THE_PARAMETER = """
            module p
            data LI = { quantity: Int, unitPrice: Int }
            data Invalid = { n: Int }
            behavior f : (items: List<LI>) -> Bool | Invalid
            let f (items) = {
                guard List.all(i -> i.quantity >= 1, items) else Invalid { n = 1 }
                List.any(i -> i.unitPrice >= 100000, items)
            }
            """;

    private static final Pattern QUANTITY = Pattern.compile("quantity = (-?\\d+)");

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

    /** Every point is offered a row, inside the parameter as at it. */
    @Test
    void everyPointIsOfferedARowWhereverTheListStands() {
        for (String model : List.of(INSIDE, THE_PARAMETER, PRICED_INSIDE, PRICED_THE_PARAMETER)) {
            Compilation compilation = measured(model);

            assertEquals(List.of(), OfferedAtTheLines.of(compilation, "p", "f").unresolved(),
                    () -> report(compilation));
        }
    }

    /**
     * The row at the filter's line where it keeps nothing of quantity one holds an element under
     * one, which fails the guard, and one at one, which the line is about.
     */
    @Test
    void theRowBesideTheFiltersLineHoldsElementsThatDiffer() {
        Compilation compilation = measured(INSIDE);
        List<List<Long>> beside = new ArrayList<>();
        for (Generator.GeneratedRow row : OfferedAtTheLines.of(compilation, "p", "f").rows()) {
            if (row.purposes().stream().noneMatch(each -> each
                    instanceof Generator.Purpose.ForAPoint(var label)
                    && label.equals("c.items[*].quantity = 1"))) {
                continue;
            }
            List<Long> quantities = new ArrayList<>();
            Matcher quantity = QUANTITY.matcher(row.inputs().getFirst().text());
            while (quantity.find()) {
                quantities.add(Long.parseLong(quantity.group(1)));
            }
            beside.add(quantities);
        }

        assertTrue(beside.stream().anyMatch(quantities -> quantities.contains(1L)
                && quantities.stream().anyMatch(each -> each < 1)), beside::toString);
    }

    /** Every row at the unit price's line holds only elements the guard keeps. */
    @Test
    void theRowsAtTheUnitPriceHoldQuantitiesTheGuardKeeps() {
        Compilation compilation = measured(PRICED_INSIDE);
        int rows = 0;
        for (Generator.GeneratedRow row : OfferedAtTheLines.of(compilation, "p", "f").rows()) {
            if (row.purposes().stream().noneMatch(each -> each
                    instanceof Generator.Purpose.ForAPoint(var label)
                    && label.contains("unitPrice"))) {
                continue;
            }
            rows++;
            String text = row.inputs().getFirst().text();
            Matcher quantity = QUANTITY.matcher(text);
            while (quantity.find()) {
                assertTrue(Long.parseLong(quantity.group(1)) >= 1, text);
            }
        }

        assertEquals(4, rows, () -> report(compilation));
    }
}
