package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One condition written at two places of a body is one condition of a rule through both, and the
 * rule is described at both places.
 *
 * <p>The two comparisons say the same thing of the input, so a way through both is one column
 * consulted twice. Described by where it was first consulted, the rule would send a reader to the
 * outer comparison and say nothing of the inner one it also goes through.
 */
class AConditionWrittenTwiceIsShownAtBothPlacesTest {

    private static final String MODEL = """
            module example.twice

            behavior f : (n: Int) -> Int

            let f (n) = if n > 0 then (if n > 0 then 1 else 2) else 3
            """;

    @Test
    void aRuleThroughBothComparisonsIsDescribedAtBoth() {
        List<String> page = page().lines().toList();
        List<String> places = places("n > 0");
        assertEquals(2, places.size(), "the body writes the comparison twice");
        boolean both = false;
        for (int at = 0; at < page.size(); at++) {
            if (!page.get(at).contains("no row takes a decision rule")) {
                continue;
            }
            List<String> described = new ArrayList<>();
            for (int under = at + 1; under < page.size()
                    && page.get(under).startsWith("          · "); under++) {
                described.add(page.get(under));
            }
            both |= described.stream().anyMatch(line -> line.contains(places.get(0) + " holds"))
                    && described.stream().anyMatch(line -> line.contains(places.get(1) + " holds"));
        }
        assertTrue(both, "the rule through both comparisons holding is described at both: "
                + String.join("\n", page));
    }

    /** Where the body writes {@code written}, each time, as a page names the place. */
    private static List<String> places(String written) {
        List<String> out = new ArrayList<>();
        List<String> lines = MODEL.lines().toList();
        for (int line = 0; line < lines.size(); line++) {
            for (int at = lines.get(line).indexOf(written); at >= 0;
                    at = lines.get(line).indexOf(written, at + 1)) {
                out.add((line + 1) + ":" + (at + 3));
            }
        }
        return out;
    }

    private static String page() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
