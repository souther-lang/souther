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
     * Billing's due dates: the comparisons in {@code isBusinessDay}, called inside the
     * {@code find} of {@code firstBusinessDay}, which each arm of {@code onABusinessDay}'s match
     * calls and {@code dueDate} calls in turn. The candidates are dates, and several steps reach
     * one date, so the choices are among dates and not among readings of {@code isBusinessDay}.
     */
    private static final String SHAPED_AS_BILLING = """
            module demo exposing (g, Calendar, Rule)
            import List ( map, find, rangeInclusive )
            data Rule = Preceding | Following
            data Calendar = { holidays: Set<Date>, aSunday: Date, rule: Rule }
            let weekday (c: Calendar, d: Date): Int =
                Int.floorMod(Date.daysBetween(c.aSunday, d), 7)
            let isBusinessDay (c: Calendar, d: Date): Bool =
                weekday(c, d) >= 1 && weekday(c, d) <= 5 && Bool.not(Set.contains(d, c.holidays))
            let firstBusinessDay (c: Calendar, from: Date, step: Int): Date =
                rangeInclusive(0, 1)
                    |> map(n -> Date.addDays(n * step, from))
                    |> find(d -> isBusinessDay(c, d))
                    |> Option.withDefault(from)
            let onABusinessDay (c: Calendar, nominal: Date): Date =
                match c.rule with
                    | Preceding -> firstBusinessDay(c, nominal, 0 - 1)
                    | Following -> firstBusinessDay(c, nominal, 1)
            let dueDate (c: Calendar, nominal: Date): Date = onABusinessDay(c, nominal)
            behavior g : (c: Calendar, nominal: Date) -> Date
            let g (c, nominal) = dueDate(c, nominal)
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

    /** What each case came to, of each of {@code told}. */
    private static List<JsonNode> caseExpansions(List<JsonNode> told) {
        return told.stream().map(reading -> reading.path("caseExpansion")).toList();
    }

    /** Each reading of each case of each line not worked out, whole. */
    private static List<JsonNode> told(AdequacyReport report, Compilation compilation) {
        JsonNode partition = JSON.readTree(report
                        .json(SourceRendering.namedByIdentity(compilation.texts())))
                .path("modules").get(0).path("behaviors").get(0).path("partition");
        List<JsonNode> out = new ArrayList<>();
        partition.path("caseExpansions").forEach(each -> each.path("readings")
                .forEach(out::add));
        assertFalse(out.isEmpty(), "the line on what the search found is past the figure: "
                + partition);
        return out;
    }

    /** That none of {@code told} names a helper a function outside it calls. */
    private static void namesNoHelperCalledOnEachElement(List<JsonNode> told) {
        told.forEach(reading -> assertFalse(reading.has("helperCalledOnEachElement"),
                reading::toString));
    }

    /** Every reading of a case not worked out of {@code model}, compiled. */
    private static List<JsonNode> toldOf(String model) {
        Compilation compilation = made(model);
        ACompiledModel.compiles(compilation);
        return told(AdequacyReport.of(compilation), compilation);
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

    /** And, the choices multiplying its readings, that is what is said of it: no second
     *  suggestion of the same helper. */
    @Test
    void theHelperTheSearchAppliesOnEachCandidateIsNamedAtTheComparisonsItWrote() {
        List<JsonNode> told = toldOf(CALLED_ON_EACH_CANDIDATE);
        namesNoHelperCalledOnEachElement(told);
        for (JsonNode reading : caseExpansions(told)) {
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
        List<JsonNode> told = told(report, compilation);
        namesNoHelperCalledOnEachElement(told);
        for (JsonNode reading : caseExpansions(told)) {
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
        List<String> lines = text.lines().filter(line -> line.contains("case expansion")).toList();
        assertFalse(lines.isEmpty(), text);
        for (String line : lines) {
            assertTrue(line.contains("The helper `ok` is read more than once")
                            && line.contains("the call written inside `first`, `pick` has to move"
                            + " into the `let` of the behavior itself"),
                    "the helper, and the helpers its call moves out of: " + line);
        }
    }

    @Test
    void comparisonsTheBehaviorWritesItselfNameNoHelper() {
        List<JsonNode> told = toldOf(IN_THE_BEHAVIORS_OWN_BODY);
        caseExpansions(told).forEach(reading -> assertEquals(0,
                reading.path("multipliedHelpers").size(), reading::toString));
        namesNoHelperCalledOnEachElement(told);
    }

    @Test
    void aHelperExpandedOnceIsOneReadingWhateverItMultipliesInside() {
        List<JsonNode> told = toldOf(EXPANDED_ONCE);
        caseExpansions(told).forEach(reading -> assertEquals(0,
                reading.path("multipliedHelpers").size(), reading::toString));
        namesNoHelperCalledOnEachElement(told);
    }

    @Test
    void readingsChosenAmongAsAlternativesAreAddedAndNameNoHelper() {
        List<JsonNode> told = toldOf(READINGS_THAT_ARE_ALTERNATIVES);
        caseExpansions(told).forEach(reading -> assertEquals(0,
                reading.path("multipliedHelpers").size(), reading::toString));
        namesNoHelperCalledOnEachElement(told);
    }

    /**
     * Billing's shape: nothing multiplies the readings of {@code isBusinessDay} and no helper holds
     * every choice, and the helper named is the one the comparisons are written in, with every
     * helper that calls it.
     */
    @Test
    void theHelperAFindOutsideItCallsOnEachCandidateIsNamedWithEveryHelperCallingIt() {
        for (JsonNode reading : toldOf(SHAPED_AS_BILLING)) {
            assertEquals(0, reading.path("caseExpansion").path("multipliedHelpers").size(),
                    reading::toString);
            assertFalse(reading.has("helperToDeclare"), reading::toString);
            JsonNode named = reading.path("helperCalledOnEachElement");
            assertEquals("demo.isBusinessDay", named.path("helper").asString(),
                    reading::toString);
            assertEquals(List.of("demo.firstBusinessDay", "demo.onABusinessDay", "demo.dueDate"),
                    JSON.convertValue(named.path("calledInside"), List.class),
                    "every helper on the way out to the behavior: " + named);
            for (JsonNode call : named.path("calls")) {
                assertTrue(writtenAt(SHAPED_AS_BILLING, call).startsWith("find("),
                        "the find around the call: " + call);
            }
            assertEquals(List.of(), JSON.convertValue(named.path("leftReadAgainBy"), List.class),
                    "no other rule suggests a helper here: " + named);
        }
    }
}
