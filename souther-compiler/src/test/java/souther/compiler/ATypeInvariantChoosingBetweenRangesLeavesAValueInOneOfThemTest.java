package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A type invariant that chooses between two ranges leaves its position the two ranges, and a value
 * chosen for the position is one of them.
 *
 * <p>Ranges far from where a value is usually chosen, so a row exists only where the choice reached
 * whoever chooses: zero for a number, and the day the rows are written on for a date, both fall in
 * the gap.
 */
class ATypeInvariantChoosingBetweenRangesLeavesAValueInOneOfThemTest {

    private static final String BESIDE_ANOTHER_INPUT = """
            behavior f : (u: U, n: Int) -> Bool
            let f (u, n) = if n >= 3 then true else false
            """;

    private static String model(String type, String invariant, String behavior) {
        return """
                module example.gap

                data U = TYPE
                    invariant RULE

                """.replace("TYPE", type).replace("RULE", invariant) + behavior;
    }

    private static String blockFor(String type, String invariant, String behavior) {
        Compilation compilation = Compilation.ofSource(model(type, invariant, behavior), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return GeneratedRows.of(compilation, "example.gap", "f",
                SourceRendering.namedByIdentity(compilation.texts())).text();
    }

    private static List<String> codesFor(String type, String invariant) {
        Compilation compilation = Compilation.ofSource(
                model(type, invariant, BESIDE_ANOTHER_INPUT), "Main");
        compilation.answerEverything();
        return compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(Located::diagnostic)
                .map(diagnostic -> diagnostic.code())
                .toList();
    }

    @Test
    void aNumberGetsARowForEveryClassOfTheOtherPosition() {
        String block = blockFor("Int", "value > 100 || value < 0", BESIDE_ANOTHER_INPUT);

        assertFalse(block.contains("no row for"), block);
        assertTrue(block.contains("n=x < 3"), block);
        assertTrue(block.contains("n=3 <= x"), block);
    }

    @Test
    void aDateGetsARowForEveryClassOfTheOtherPosition() {
        String block = blockFor("Date",
                "value > Date(\"2300-01-01\") || value < Date(\"1900-01-01\")",
                BESIDE_ANOTHER_INPUT);

        assertFalse(block.contains("no row for"), block);
        assertTrue(block.contains("n=x < 3"), block);
        assertTrue(block.contains("n=3 <= x"), block);
    }

    /**
     * A body that draws its line in the gap gets a row on each side of it, each the value of the
     * run on that side nearest the line: the values beside the line are the gap's, and neither is a
     * value of the type — which is said of the points at the line, and not that their values were
     * refused.
     */
    @Test
    void aBodyDrawingItsLineInTheGapGetsARowInEachRun() {
        String block = blockFor("Int", "value > 100 || value < 0", """
                behavior f : (u: U) -> Bool
                let f (u) = if u.value > 50 then true else false
                """);

        assertTrue(block.contains("(U(-1))"), block);
        assertTrue(block.contains("(U(101))"), block);
        assertFalse(block.contains("refused at construction"), block);
        assertTrue(block.contains("no row for `u = 50` in `f`: no value can stand here"), block);
        assertTrue(block.contains("no row for `u = 51` in `f`: no value can stand here"), block);
    }

    /** A choice whose ranges a rule beside it leaves no value of is refused where it is written. */
    @Test
    void aChoiceTheRestOfTheRulesLeaveNothingOfIsRefused() {
        assertEquals(List.of("E1013"),
                codesFor("Int", "(value > 100 || value < 0) && value >= 0 && value <= 100"));
        assertEquals(List.of(),
                codesFor("Int", "(value > 100 || value < 0) && value >= 0 && value <= 101"),
                "one value is left, and it is a value of the type");
    }
}
