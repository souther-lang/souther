package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Rows are offered that keep each choice of the elements a comparison keeps.
 *
 * <p>A comparison in a closure draws one line per element, and a row that stands on the right side
 * of one of them and the wrong side of the other is a row the total is made of. The offering has
 * to contain a row for each of the four choices, not only rows at the lines.
 */
class RowsAreOfferedForEveryChoiceOfKeptElementsTest {

    private static final String MODEL = """
            module example.attendance

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ first, second ])))
            """;

    private static final Pattern DAYS = Pattern.compile("days = (\\d+)");

    @Test
    void aRowIsOfferedForEveryChoiceOfWhichElementsAreKept() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String offered = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule(compilation.modules().get(0))),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();

        Set<List<Boolean>> kept = new HashSet<>();
        offered.lines().filter(line -> line.startsWith("    | ")).forEach(row -> {
            Matcher days = DAYS.matcher(row);
            List<Boolean> choice = new ArrayList<>();
            while (days.find()) {
                choice.add(Integer.parseInt(days.group(1)) >= 17);
            }
            kept.add(choice);
        });

        assertEquals(Set.of(List.of(true, true), List.of(true, false), List.of(false, true),
                List.of(false, false)), kept, offered);
    }
}
