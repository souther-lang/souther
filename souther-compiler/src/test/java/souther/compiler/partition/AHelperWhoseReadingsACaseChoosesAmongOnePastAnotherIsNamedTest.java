package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line is not worked out for the number of its cases and those cases choose among a
 * helper's readings one past another, the report names the helper as one to declare a behavior —
 * the helper that wrote the comparisons, which is not the one the factors name — and where it is
 * not, it names none.
 *
 * <p>Every model here searches seven thresholds with three comparisons failing at each, so the
 * line on what the search found is past the cases taken apart as the choices stand wherever the
 * comparisons are written. What changes from one model to the next is who wrote them and how often a reading of
 * them is chosen past another.
 */
class AHelperWhoseReadingsACaseChoosesAmongOnePastAnotherIsNamedTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String OK = """
            let ok (x: Int, y: Int, t: Int): Bool = x > t && y > t && x + y > t
            """;

    /** The search's closure calls a helper: one reading of it on each candidate. */
    private static final String CALLED_ON_EACH_CANDIDATE = "module demo exposing (g)\n" + OK + """
            behavior g : (x: Int, y: Int) -> Bool
            let g (x, y) =
                Option.withDefault(0, List.find(t -> ok(x, y, t), [1, 2, 3, 4, 5, 6, 7])) > 3
            """;

    /**
     * Shaped as billing writes its due dates: the search in one helper, the comparisons in
     * another, and the first called from a third on each arm of a choice.
     */
    private static final String CALLED_INSIDE_HELPERS = "module demo exposing (g)\n" + OK + """
            let first (x: Int, y: Int, step: Int): Int =
                Option.withDefault(0, List.find(t -> ok(x, y, t * step), [1, 2, 3, 4, 5, 6, 7]))
            let pick (x: Int, y: Int): Int = if x > y then first(x, y, 1) else first(y, x, 2)
            behavior g : (x: Int, y: Int) -> Bool
            let g (x, y) = pick(x, y) > 3
            """;

    /** The same comparisons written in the behavior's own closure. */
    private static final String IN_THE_BEHAVIORS_OWN_BODY = """
            module demo exposing (g)
            behavior g : (x: Int, y: Int) -> Bool
            let g (x, y) =
                Option.withDefault(0, List.find(t -> x > t && y > t && x + y > t,
                    [1, 2, 3, 4, 5, 6, 7])) > 3
            """;

    /**
     * The search and its comparisons in one helper called once: every candidate is read inside
     * the one copy, so there is one reading, however many ways it multiplies to.
     */
    private static final String EXPANDED_ONCE = """
            module demo exposing (g)
            let first (x: Int, y: Int): Int =
                Option.withDefault(0, List.find(t -> x > t && y > t && x + y > t,
                    [1, 2, 3, 4, 5, 6, 7]))
            behavior g : (x: Int, y: Int) -> Bool
            let g (x, y) = first(x, y) > 3
            """;

    /**
     * Two readings of a helper as alternatives to each other: the second is chosen only where the
     * first fails, inside that one alternative, so their ways are added and the search's
     * multiply them both alike.
     */
    private static final String READINGS_THAT_ARE_ALTERNATIVES = """
            module demo exposing (g)
            let h (v: Int): Bool = v > 50
            behavior g : (x: Int, y: Int) -> Bool
            let g (x, y) =
                Option.withDefault(0, List.find(t -> x > t && y > t && x + y > t,
                    [1, 2, 3, 4, 5, 6, 7])) > (if h(y) || h(x) then 3 else 4)
            """;

    /**
     * How many cases a line is taken apart into here: none. The comparisons of one search leave
     * few ways once their numbers are read, so at the figure declared the line would be taken
     * apart and say nothing of a helper; held to none, every line past the figure as the choices
     * stand is cut off ({@link Allowances}).
     */
    private static final int NO_CASE_TAKEN_APART = 0;

    private static Compilation made(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main").allowing(
                Allowances.DECLARED.with(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO,
                        NO_CASE_TAKEN_APART));
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        return compilation;
    }

    /** What each case of each line not worked out came to, at each copy it was read at. */
    private static List<JsonNode> readings(Compilation compilation) {
        return readings(AdequacyReport.of(compilation), compilation);
    }

    private static List<JsonNode> readings(AdequacyReport report, Compilation compilation) {
        JsonNode partition = JSON.readTree(report
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .path("modules").get(0).path("behaviors").get(0).path("partition");
        List<JsonNode> out = new ArrayList<>();
        partition.path("caseExpansions").forEach(each -> each.path("readings")
                .forEach(reading -> out.add(reading.path("caseExpansion"))));
        assertFalse(out.isEmpty(), "the line on what the search found is past the figure: "
                + partition);
        return out;
    }

    /** What {@code model} has written from {@code construct}'s place to the end of its line. */
    private static String writtenAt(String model, JsonNode construct) {
        JsonNode at = construct.path("at");
        assertTrue(at.has("line") && at.has("column"), "where the author wrote it: " + construct);
        String line = model.lines().toList().get(at.path("line").asInt() - 1);
        return line.substring(at.path("column").asInt() - 1);
    }

    /** The one helper {@code reading} names, which every reading here names exactly one of. */
    private static JsonNode onlyHelper(JsonNode reading) {
        JsonNode helpers = reading.path("multipliedHelpers");
        assertEquals(1, helpers.size(), "one helper multiplied: " + reading);
        return helpers.get(0);
    }

    @Test
    void theHelperTheSearchAppliesOnEachCandidateIsNamedAtTheComparisonsItWrote() {
        Compilation compilation = made(CALLED_ON_EACH_CANDIDATE);
        ACompiledModel.compiles(compilation);
        for (JsonNode reading : readings(compilation)) {
            JsonNode helper = onlyHelper(reading);
            assertEquals("demo.ok", helper.path("helper").asString());
            Set<String> written = new TreeSet<>();
            for (JsonNode at : helper.path("madeAt")) {
                assertEquals("ok", at.path("construct").path("definition").asString(),
                        "a comparison the helper wrote: " + at);
                assertEquals(List.of(), JSON.convertValue(at.path("calledInside"), List.class),
                        "called in the behavior's own body: " + at);
                written.add(writtenAt(CALLED_ON_EACH_CANDIDATE, at));
            }
            assertEquals(Set.of("> t", "> t && y > t && x + y > t", "> t && x + y > t"), written,
                    "each comparison of ok, at its operator");
            for (JsonNode factor : reading.path("factors")) {
                assertFalse(factor.toString().contains("demo.ok"),
                        "what multiplied the parts is the search, and ok is in none of it: "
                                + factor);
            }
        }
    }

    @Test
    void aHelperCalledInsideOtherHelpersIsNamedWithTheHelpersItsCallHasToMoveOutOf() {
        Compilation compilation = made(CALLED_INSIDE_HELPERS);
        ACompiledModel.compiles(compilation);
        AdequacyReport report = AdequacyReport.of(compilation);
        for (JsonNode reading : readings(report, compilation)) {
            JsonNode helper = onlyHelper(reading);
            assertEquals("demo.ok", helper.path("helper").asString());
            Set<String> copies = new TreeSet<>();
            for (JsonNode at : helper.path("madeAt")) {
                assertEquals(List.of("demo.first", "demo.pick"),
                        JSON.convertValue(at.path("calledInside"), List.class),
                        "the helper calling ok first, then the one calling it: " + at);
                copies.add(at.path("construct").path("through").toString());
            }
            assertEquals(2, copies.size(), "a copy of ok in each copy of first, one on each arm"
                    + " of pick's if: " + helper);
        }
        String text = report.humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> told = text.lines().filter(line -> line.contains("case expansion")).toList();
        assertFalse(told.isEmpty(), text);
        for (String line : told) {
            assertTrue(line.contains("the helper `ok`") && line.contains("written inside `first`,"
                            + " `pick`, so it moves into a behavior's own let"),
                    "the helper, and the helpers its call moves out of: " + line);
        }
    }

    @Test
    void comparisonsTheBehaviorWritesItselfNameNoHelper() {
        Compilation compilation = made(IN_THE_BEHAVIORS_OWN_BODY);
        ACompiledModel.compiles(compilation);
        readings(compilation).forEach(reading -> assertEquals(0,
                reading.path("multipliedHelpers").size(), reading::toString));
    }

    @Test
    void aHelperExpandedOnceIsOneReadingWhateverItMultipliesInside() {
        Compilation compilation = made(EXPANDED_ONCE);
        ACompiledModel.compiles(compilation);
        readings(compilation).forEach(reading -> assertEquals(0,
                reading.path("multipliedHelpers").size(), reading::toString));
    }

    @Test
    void readingsChosenAmongAsAlternativesAreAddedAndNameNoHelper() {
        Compilation compilation = made(READINGS_THAT_ARE_ALTERNATIVES);
        ACompiledModel.compiles(compilation);
        readings(compilation).forEach(reading -> assertEquals(0,
                reading.path("multipliedHelpers").size(), reading::toString));
    }
}
