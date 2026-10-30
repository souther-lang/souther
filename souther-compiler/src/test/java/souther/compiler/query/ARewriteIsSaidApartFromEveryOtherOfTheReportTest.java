package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two rewrites the report holds apart are two lines a reader can tell apart, and two entries the
 * document joins to the rewrite each is about.
 *
 * <p>Three places where the words or the identity of a rewrite stop short of what the measure
 * tells apart: two forks of one library definition that read alike, two modules whose behaviors of
 * one name call one library definition, and the document's entry that keeps a verdict open against
 * the entry of the rewrite under its measure.
 */
class ARewriteIsSaidApartFromEveryOtherOfTheReportTest {

    /** The fold-over-a-list body, with the rows that leave both folds' rewrites open. */
    private static String foldModel(String module, String extraRows) {
        return """
                module %s

                data Rec = { n: Int, xs: List<Int> }

                behavior count : (r: Rec, k: Int) -> Int

                let count (r, k) = List.length(List.filter(x -> x == k, r.xs))

                behavior done : (r: Rec) -> Bool

                let done (r) = List.all(k -> count(r, k) >= 2, List.rangeInclusive(1, r.n))

                example count
                    | (Rec { n = 1, xs = [1, 1] }, 1) -> 2
                    | (Rec { n = 1, xs = [] }, 1) -> 0
                    | (Rec { n = 0, xs = [] }, 0) -> 0
                    | (Rec { n = 0, xs = [0] }, 0) -> 1
                    | (Rec { n = 0, xs = [-1] }, 0) -> 0
                    | (Rec { n = 0, xs = [1] }, 0) -> 0
                    | (Rec { n = 0, xs = [-2] }, 0) -> 0
                    | (Rec { n = 0, xs = [2] }, 0) -> 0

                example done
                    | (Rec { n = 1, xs = [1, 1] }) -> true
                    | (Rec { n = 1, xs = [] }) -> false
                    | (Rec { n = 0, xs = [] }) -> true
                %s
                """.formatted(module, extraRows);
    }

    /** A body calling the one library definition twice, so its forks are rewritten once each. */
    private static final String CLAMPED_TWICE = """
            module probe.clamped

            data Kept = { n: Int }
            data Dropped
            data Outcome = Kept | Dropped

            behavior f : (n: Int, m: Int) -> Outcome

            let f (n, m) =
                if n > 100 then Dropped
                else Kept { n = Int.clamp(0, 100, n) + Int.clamp(0, 100, m) }

            example f
                | "small numbers are kept" : (5, 5) -> Kept
                | "negative numbers are kept" : (-3, -3) -> Kept
                | "a large number is dropped" : (200, 0) -> Dropped
            """;

    /**
     * The same two forks, told to a build as warnings: the sentence is pointed at the behavior
     * and names the definition, so two of them read alike but for the construct each is of.
     */
    @Test
    void twoForksOfOneLibraryDefinitionAreTwoWarnings() {
        Compilation compilation = compiled(CLAMPED_TWICE);
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();

        List<String> said = compilation.warnings().stream()
                .map(Located::diagnostic)
                .filter(d -> "E1939".equals(d.code().toString()))
                .map(d -> Messages.render(d.said(), Locale.ENGLISH))
                .filter(sentence -> sentence.contains("souther.int.clamp"))
                .toList();

        assertTrue(said.size() >= 2, () -> "forks of the library definition are warned of: " + said);
        assertEquals(said.size(), new HashSet<>(said).size(),
                () -> "no two warnings are the same sentence: " + said);
    }

    /**
     * And in the reader's language: what tells the two apart is said in the words of that
     * language, with no word of another in the sentence.
     */
    @Test
    void theWarningsAreToldApartInJapaneseInJapanese() {
        Compilation compilation = compiled(CLAMPED_TWICE);
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();

        List<String> said = compilation.warnings().stream()
                .map(Located::diagnostic)
                .filter(d -> "E1939".equals(d.code().toString()))
                .map(d -> Messages.render(d.said(), Locale.JAPANESE))
                .filter(sentence -> sentence.contains("souther.int.clamp"))
                .toList();

        assertTrue(said.size() >= 2, () -> "forks of the library definition are warned of: " + said);
        assertEquals(said.size(), new HashSet<>(said).size(),
                () -> "no two warnings are the same sentence: " + said);
        assertTrue(said.stream().anyMatch(sentence -> sentence.contains("構文")),
                () -> "what tells them apart is said in Japanese: " + said);
        assertTrue(said.stream().noneMatch(sentence -> sentence.contains("construct")),
                () -> "and in no other language: " + said);
    }

    private static AdequacyReport reported(Compilation compilation) {
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }

    private static Compilation compiled(String... sources) {
        return Compilation.ofSources(List.of(sources), ModulePath.EMPTY);
    }

    /**
     * Two forks of one library definition, each an arm answering as its sibling, are said with the
     * same arms and the same definition. The construct each is of is what tells them apart, and is
     * said beside the ones that would read alike and beside no other.
     */
    @Test
    void twoForksOfOneLibraryDefinitionAreTwoLines() {
        Compilation compilation = compiled(CLAMPED_TWICE);
        AdequacyReport report = reported(compilation);

        List<String> lines = report.human(SourceRendering.namedByIdentity(compilation.texts()))
                .lines().map(String::strip)
                .filter(line -> line.contains("souther.int.clamp")).toList();

        assertTrue(lines.size() >= 2, () -> "forks of the library definition are said: " + lines);
        assertEquals(lines.size(), new HashSet<>(lines).size(),
                () -> "no two of them are the same line: " + lines);
        assertTrue(lines.stream().anyMatch(line -> line.contains("(construct ")),
                () -> "the ones that read alike say which construct: " + lines);
    }

    /**
     * Two modules each declare a behavior of one name calling one library definition. Their
     * rewrites are the same obligation identity, and are four things that keep the verdict open.
     */
    @Test
    void sameNamedBehaviorsOfTwoModulesKeepTheVerdictOpenSeparately() {
        Compilation compilation = compiled(foldModel("probe.one", ""),
                foldModel("probe.two", ""));
        AdequacyReport report = reported(compilation);
        List<String> lines = report.human(SourceRendering.namedByIdentity(compilation.texts()))
                .lines().map(String::strip).toList();

        Matcher atAFigure = Pattern.compile("stopped at a figure of this compiler\\s+(\\d+)")
                .matcher(String.join("\n", lines));
        assertTrue(atAFigure.find(), () -> "the count is said: " + lines);
        assertEquals("4", atAFigure.group(1),
                () -> "two rewrites in each of two modules: " + lines);

        List<String> kept = lines.stream()
                .filter(line -> line.startsWith("probe.one.done, where")
                        || line.startsWith("probe.two.done, where"))
                .toList();
        assertEquals(4, kept.size(), () -> "one line apiece, saying whose it is: " + kept);
        assertEquals(4, new HashSet<>(kept).size(), () -> "and no two alike: " + kept);
    }

    /**
     * What keeps a verdict open names the rewrite by the id its entry has under the measure, in the
     * module whose behavior it is of: a consumer joins the two on it.
     */
    @Test
    void anEntryThatKeepsTheVerdictOpenJoinsTheRewriteUnderTheMeasure() throws Exception {
        Compilation compilation = compiled(foldModel("probe.one", ""),
                foldModel("probe.two", ""));
        AdequacyReport report = reported(compilation);
        JsonNode root = JsonMapper.builder().build()
                .readTree(report.json(SourceRendering.namedByIdentity(compilation.texts())));

        Set<String> joined = new HashSet<>();
        int entries = 0;
        for (JsonNode each : root.get("keptOpenBy")) {
            JsonNode about = each.get("about");
            if (!about.get("kind").asString().equals("replacement")) {
                continue;
            }
            entries++;
            JsonNode found = null;
            for (JsonNode module : root.get("modules")) {
                if (!module.get("module").asString().equals(about.get("module").asString())) {
                    continue;
                }
                for (JsonNode behavior : module.get("behaviors")) {
                    if (!behavior.has("replacement")
                            || !behavior.get("replacement").has("obligations")) {
                        continue;
                    }
                    for (JsonNode obligation : behavior.get("replacement").get("obligations")) {
                        if (obligation.get("obligationId").equals(about.get("replacementId"))) {
                            found = obligation;
                        }
                    }
                }
            }
            JsonNode entry = found;
            assertTrue(entry != null, () -> "the rewrite " + about + " is under its measure");
            assertEquals("undecided", entry.get("disposition").asString(),
                    () -> "and is the one left open: " + entry);
            joined.add(about.get("module").asString() + "/" + about.get("replacementId"));
        }
        assertEquals(4, entries, "one entry per rewrite left open, in either module");
        assertEquals(4, joined.size(), () -> "each joined to a rewrite of its own: " + joined);
    }

    /**
     * Rows that tell the two folds apart settle them: nothing is left open, so nothing is said
     * about a rewrite left open, on the page or in the document.
     */
    @Test
    void aRewriteTheRowsSettleIsNoLongerSaidToBeLeftOpen() throws Exception {
        Compilation compilation = compiled(foldModel("repro.settled", """
                    | (Rec { n = 2, xs = [1, 1] }) -> false
                    | (Rec { n = 2, xs = [2, 2] }) -> false
                """));
        AdequacyReport report = reported(compilation);
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());

        String page = report.human(rendering);
        assertTrue(page.contains("replacement 4/4"), () -> "every rewrite is noticed: " + page);
        assertFalse(page.contains("? not decided"), () -> "none is left open: " + page);

        List<String> open = new ArrayList<>();
        for (JsonNode each : JsonMapper.builder().build().readTree(report.json(rendering))
                .get("keptOpenBy")) {
            if (each.get("about").get("kind").asString().equals("replacement")) {
                open.add(each.toString());
            }
        }
        assertEquals(List.of(), open, "and the document holds none of them open");
    }
}
