package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk from a seed whose step adds a number to what it carried on the elements meeting a
 * statement, and keeps it on the rest, is how many elements meet the statement.
 *
 * <p>So a comparison over it is the comparison over the count, and draws the line a count of the
 * filtered list draws. A step that starts over on an element is no count: what it ends with turns
 * on the order of the elements and not on how many of them meet anything.
 */
class AFoldCountingWhatEachElementMeetsIsTheCountTest {

    private static final String ROWS = """

            example out
                | ([]) -> false
                | ([0]) -> false
                | ([1]) -> false
                | ([0, 0]) -> false
                | ([0, 0, 0]) -> true
                | ([0, 1, 0, 0]) -> true
            """;

    private static String report(String body) {
        String source = """
                module m

                behavior out : (xs: List<Int>) -> Bool

                let out (xs) = %s
                """.formatted(body) + ROWS;
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String lineAbout(String report, String word) {
        return report.lines().filter(line -> line.contains(word)).findFirst().orElse("");
    }

    @Test
    void aStepAddingOneWhereTheElementMeetsItIsTheCount() {
        String report = report(
                "List.fold((n, x) -> if x == 0 then n + 1 else n, 0, xs) >= 3");

        assertFalse(report.contains("not read"), report);
        assertTrue(report.contains("#xs [xs[*] == 0]"), report);
    }

    @Test
    void itDrawsTheLinesTheCountOfTheFilteredListDraws() {
        String folded = report(
                "List.fold((n, x) -> if x == 0 then n + 1 else n, 0, xs) >= 3");
        String filtered = report("List.length(List.filter(x -> x == 0, xs)) >= 3");

        assertEquals(lineAbout(filtered, "border "), lineAbout(folded, "border "), folded);
        assertEquals(lineAbout(filtered, "partition "), lineAbout(folded, "partition "), folded);
    }

    /** Which arm adds is the walk's to say, and keeping on the other is the same count. */
    @Test
    void theArmThatAddsMayBeEither() {
        String report = report(
                "List.fold((n, x) -> if x /= 0 then n else n + 1, 0, xs) >= 3");

        assertFalse(report.contains("not read"), report);
        assertTrue(report.contains("#xs ["), report);
    }

    /**
     * A step that starts over where an element fails is how many met it since the last that did
     * not — which is no count of the elements, and is not read as one.
     */
    @Test
    void aStepThatStartsOverIsNoCount() {
        String report = report(
                "List.fold((n, x) -> if x == 0 then n + 1 else 0, 0, xs) >= 3");

        assertFalse(report.contains("#xs ["), report);
    }

    /** What decides the arm may not read what the walk carried, or which arm an element takes is
     *  no statement about the element. */
    @Test
    void aStepDecidedByWhatItCarriedIsNoCount() {
        String report = report(
                "List.fold((n, x) -> if n < 2 then n + 1 else n, 0, xs) >= 3");

        assertFalse(report.contains("#xs ["), report);
    }
}
