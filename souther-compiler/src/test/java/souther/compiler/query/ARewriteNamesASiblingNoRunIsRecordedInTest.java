package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rewrite names the arm it answers as even where that arm is one no run through is recorded.
 *
 * <p>{@code if true} sends every run to its {@code then}, so its {@code else} is an arm the plan
 * has no site for. The {@code then} rewritten as the {@code else} is still a rewrite, and the row
 * holding nothing does not tell it apart; what it answered as is read off the arms the walk met,
 * and not off the sites, which hold no {@code else} here.
 */
class ARewriteNamesASiblingNoRunIsRecordedInTest {

    private static final String SOURCE = """
            module example.always

            behavior f : (n: Int) -> Int

            let f (n) = if true then n else 0

            example f
                | (0) -> 0
            """;

    @Test
    void theSiblingIsNamedThoughNoSiteIsItsOwn() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");

        List<Integer> measured = compilation.db().ask(new Bodies.Checked("example.always"))
                .value().plan().arms("f").stream()
                .map(each -> each.obligation().part())
                .toList();
        assertEquals(List.of(0), measured, "only the `then` is an arm a run is recorded in");

        String page = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(page.contains(
                        "! no row would come out differently if `then` (5:13) answered as `else`"),
                () -> "the `else` named all the same: " + page);
    }
}
