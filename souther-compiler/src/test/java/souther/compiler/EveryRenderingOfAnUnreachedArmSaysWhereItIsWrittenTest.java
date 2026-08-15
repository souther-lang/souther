package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One unreached arm, said three times, and the three saying the same thing.
 *
 * <p>An arm of a body spliced in from out of sight is at a call in the caller's file and is not
 * written there. The warning a build reads said so; the report a person reads and the report a build
 * reads printed the coordinate and left it at that, so the same arm was at {@code List.filter} in one
 * of the three and at {@code m.sou:15:23} in the other two. Nothing held them against each other, and
 * each was written believing the coordinate was the place.
 *
 * <p>Held together here rather than one assertion per rendering. Three renderings that each say
 * something true separately can still disagree, and disagreeing is the defect: a reader moving
 * between a terminal, a JSON report and an editor is reading one compile.
 *
 * <p>No module path is needed. The standard library is out of sight of every compile, so this is what
 * any model that filters or maps looks like.
 */
class EveryRenderingOfAnUnreachedArmSaysWhereItIsWrittenTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** {@code List.filter}'s {@code else} arm is owed a row and no row goes through it: every item
     *  of the one row is {@code Live}. The arm is written in {@code souther.list}. */
    private static final String OUT_OF_SIGHT = """
            module demo

            data Live
            data Gone
            data Mark = Live | Gone

            data Item = { mark: Mark }

            data Count = Int
                invariant value >= 0

            behavior tally : (items: List<Item>) -> Count
                constructs Count, Live
            let tally (items) =
                Count(List.length(List.filter(i -> i.mark == Live, items)))

            example tally
                | "every item is live" : ([ Item { mark = Live } ]) -> Count(1)
            """;

    /** The control: the same shape of gap, with the arm written in the module's own source. Whatever
     *  the three renderings gain above, they must not gain it here. */
    private static final String IN_SIGHT = """
            module demo

            data Small
            data Large
            data Size = Small | Large

            behavior classify : (n: Int) -> Size
                constructs Small, Large
            let classify (n) =
                if n <= 10 then Small else Large

            example classify
                | "under the line" : (5) -> Small
            """;

    private static final String DECLARATION = "List.filter";

    // --- the three statements ---------------------------------------------------------------------

    @Test
    void theWarningNamesTheDeclarationTheArmIsWrittenIn() {
        assertTrue(armWarningOf(OUT_OF_SIGHT).contains("`" + DECLARATION + "`"),
                () -> "the warning says where the arm is written: " + armWarningOf(OUT_OF_SIGHT));
    }

    @Test
    void theReportAPersonReadsNamesIt() {
        assertTrue(armLineOf(OUT_OF_SIGHT).contains("`" + DECLARATION + "`"),
                () -> "the line says where the arm is written: " + armLineOf(OUT_OF_SIGHT));
    }

    @Test
    void theReportABuildReadsNamesIt() {
        JsonNode writtenAt = armWrittenAtOf(OUT_OF_SIGHT);
        assertEquals("outOfSight", writtenAt.get("kind").asString(),
                "the document says the coordinate is a stand-in");
        assertEquals(DECLARATION, writtenAt.get("declaration").asString(),
                "and what it stands in for");
    }

    /**
     * The three against each other, which is the property none of them has on its own.
     *
     * <p>A rendering that stopped saying it would still pass its own test if the other two were the
     * ones read. What has to hold is that a reader moving between them is told the same thing.
     */
    @Test
    void theThreeSayTheSameThingAboutOneArm() {
        String warning = armWarningOf(OUT_OF_SIGHT);
        String line = armLineOf(OUT_OF_SIGHT);
        JsonNode writtenAt = armWrittenAtOf(OUT_OF_SIGHT);

        String named = writtenAt.get("declaration").asString();
        assertTrue(warning.contains("`" + named + "`") && line.contains("`" + named + "`"),
                () -> "one declaration, said three times: " + named + " / " + warning + " / " + line);
    }

    // --- and the control ---------------------------------------------------------------------------

    @Test
    void anArmWrittenHereGainsNoneOfIt() {
        String warning = armWarningOf(IN_SIGHT);
        String line = armLineOf(IN_SIGHT);
        JsonNode writtenAt = armWrittenAtOf(IN_SIGHT);

        assertFalse(warning.contains("no source for"),
                () -> "nothing to qualify, the arm being in a file the reader holds: " + warning);
        assertFalse(line.contains("reached at"),
                () -> "the line is the place, so it is printed as one: " + line);
        assertEquals("here", writtenAt.get("kind").asString());
        assertFalse(writtenAt.has("declaration"),
                "there is no declaration to name where the coordinate is the place");
    }

    /**
     * The document answers whichever it is.
     *
     * <p>Absence is what a report written before the key existed carries, so an emitter that wrote it
     * only where the answer was interesting would put "the code is here" and "nobody asked yet" under
     * one silence.
     */
    @Test
    void everyPositionTheDocumentWritesAnswersTheQuestion() {
        for (String model : List.of(OUT_OF_SIGHT, IN_SIGHT)) {
            JsonNode root = JSON.readTree(reportOf(model).json(SourceNameResolver.identity()));
            List<JsonNode> places = new ArrayList<>();
            collectAt(root, places);
            assertFalse(places.isEmpty(), "the document points somewhere");
            for (JsonNode at : places) {
                assertTrue(at.has("writtenAt"),
                        () -> "every place says whether it is where the code is: " + at);
            }
        }
    }

    // --- reading one arm out of each rendering ------------------------------------------------------

    /** The compile the three renderings are read from. One compile, so that a difference between them
     *  is a difference in the saying and never in what was measured. */
    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        compilation.answerEverything();
        return compilation;
    }

    private static AdequacyReport reportOf(String model) {
        return AdequacyReport.of(compiled(model));
    }

    /** The body of the one {@code E1918} the compile reports, as every reader of a diagnostic reads
     *  it — the terminal, the JSON, an editor and the text an exception carries all come from here. */
    private static String armWarningOf(String model) {
        List<String> said = new ArrayList<>();
        for (Db.Found found : compiled(model).db().allReports()) {
            Diagnostic d = found.report().diagnostic();
            if ("E1918".equals(d.code())) {
                said.add(DiagnosticRenderer.body(d, Locale.ENGLISH));
            }
        }
        assertEquals(1, said.size(), () -> "one arm is unreached: " + said);
        return said.get(0);
    }

    /** The line the human report prints under `branch` for that same arm. */
    private static String armLineOf(String model) {
        List<String> lines = reportOf(model).human(SourceNameResolver.identity()).lines()
                .map(String::strip)
                .filter(line -> line.startsWith("· no row goes through"))
                .toList();
        assertEquals(1, lines.size(), () -> "one arm is unreached: " + lines);
        return lines.get(0);
    }

    /** What the machine-readable report says about where that same arm is written. */
    private static JsonNode armWrittenAtOf(String model) {
        JsonNode root = JSON.readTree(reportOf(model).json(SourceNameResolver.identity()));
        JsonNode unreached = root.get("modules").get(0).get("behaviors").get(0)
                .get("branch").get("unreached");
        assertEquals(1, unreached.size(), () -> "one arm is unreached: " + unreached);
        JsonNode writtenAt = unreached.get(0).get("at").get("writtenAt");
        assertNotNull(writtenAt, "the place says whether it is where the code is");
        return writtenAt;
    }

    /** Every {@code at} the document holds, wherever it sits. */
    private static void collectAt(JsonNode node, List<JsonNode> into) {
        if (node.isObject()) {
            JsonNode at = node.get("at");
            if (at != null && at.isObject()) {
                into.add(at);
            }
            node.propertyStream().forEach(entry -> collectAt(entry.getValue(), into));
            return;
        }
        if (node.isArray()) {
            node.forEach(each -> collectAt(each, into));
        }
    }
}
