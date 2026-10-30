package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A comparison the reading stopped on is filed at the positions the values it compares are, or
 * were made from — and not at a position that only chose which of several values one side is.
 *
 * <p>Such a side is read once for each value it may be, and what stopped stopped on one of those.
 * The choice divides the position that made it, as a choice anywhere does.
 */
class AComparisonThatStoppedIsFiledWhereItsValuesCameFromTest {

    private static String report(String chosen) {
        String source = """
                module m

                data Side = First | Second

                behavior ofSide : (xs: List<Int>, side: Side) -> List<Int>

                let ofSide (xs, side) = {
                    let r = %s
                    List.flatMap(x -> x,
                        List.mapIndexed((i, x) -> if Int.floorMod(i, 2) == r then [x] else [], xs))
                }
                """.formatted(chosen);
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
    void aPositionThatOnlyChoseTheNumberIsNotWhereTheComparisonStopped() {
        String report = report("""
                match side with
                        | First -> 0
                        | Second -> 1""");

        assertFalse(report.contains("about `side`"), report);
    }

    /** Filed the way the same comparison against one written number is. */
    @Test
    void itIsFiledAsTheComparisonAgainstOneNumberIs() {
        String chosen = report("""
                match side with
                        | First -> 0
                        | Second -> 1""");
        String written = report("0");

        assertEquals(lineAbout(written, "border "), lineAbout(chosen, "border "), chosen);
        assertEquals(chosen.contains("not read"), written.contains("not read"), chosen);
    }
}
