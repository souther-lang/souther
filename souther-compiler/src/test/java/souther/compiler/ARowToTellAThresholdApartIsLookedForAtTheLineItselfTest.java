package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where the side of a border away from its line owes nothing, a row that tells another line from
 * the model's is looked for at the line, whatever kind of line the other one is.
 *
 * <p>Under {@code a + b > 50} failing, the values {@code a + b < 50} refuses are the line {@code
 * a + b = 50} alone. The rows leave a threshold on {@code a} standing beside that line, and the
 * row that rules the threshold out is on the line with {@code a} below it. A search that went to
 * the line only for a line left at one value offered nothing for this one.
 */
class ARowToTellAThresholdApartIsLookedForAtTheLineItselfTest {

    private static final String SOURCE = """
            module m

            data Score = Int
                invariant value >= 0 && value <= 49

            data Points = Int
                invariant value >= 0 && value <= 12

            behavior f : (a: Score, b: Points) -> Int

            let f (a, b) =
                if b.value >= 1 then
                    if a.value + b.value > 50 then 1
                    else if a.value + b.value < 50 then 2
                    else 3
                else 0

            example f
                | (Score(10), Points(3)) -> 2
                | (Score(38), Points(0)) -> 0
                | (Score(39), Points(0)) -> 0
                | (Score(49), Points(0)) -> 0
                | (Score(0), Points(0)) -> 0
                | (Score(0), Points(1)) -> 2
                | (Score(38), Points(1)) -> 2
                | (Score(38), Points(2)) -> 2
                | (Score(39), Points(1)) -> 2
                | (Score(49), Points(1)) -> 3
                | (Score(49), Points(2)) -> 1
                | (Score(40), Points(12)) -> 1
                | (Score(37), Points(12)) -> 2
            """;

    private static final Pattern ROW = Pattern.compile(
            "\\(Score\\((\\d+)\\), Points\\((\\d+)\\)\\) -> <\\?>");

    @Test
    void aRowOnTheLineWithTheThresholdRuledOutIsOffered() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main").writtenOn(TestDay.DATE);
        compilation.measure(Adequacy.Asked.fullReport());
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule(compilation.modules().get(0)));
        assertNotNull(offering, "the model compiles");
        String block = GeneratedRows.of(offering, Map.of(),
                SourceRendering.namedByIdentity(compilation.texts()), compilation.db()).text();

        Matcher rows = ROW.matcher(block);
        boolean offered = false;
        while (rows.find()) {
            int a = Integer.parseInt(rows.group(1));
            int b = Integer.parseInt(rows.group(2));
            offered |= a + b == 50 && a <= 39;
        }
        assertTrue(offered, () -> "a row at a + b = 50 with a <= 39 is offered, and the block is:\n"
                + block);
    }
}
