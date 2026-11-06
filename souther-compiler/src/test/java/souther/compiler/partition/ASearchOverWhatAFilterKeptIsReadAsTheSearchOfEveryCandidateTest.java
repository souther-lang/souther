package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.meaning.DecidingCase;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereEachLineDecides;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Searching what a filter kept for the first element a closure holds of is searching every
 * candidate for the first that was kept and that the closure holds of, and is read as that: the
 * element found is each candidate in turn, where it was kept, the closure holds of it, and of no
 * candidate before it were both. So for the behavior reading what was found, the two ways of
 * writing the search state one statement, its lines are taken apart into the same cases, and a
 * rule of it leaves every position what it left written the other way — the same lines and the
 * same words — whatever it reads of what was found: the value itself, a value of it, or a field of
 * a record built of it. So too through two filters, and where what a filter kept by is a statement
 * that is not read.
 *
 * <p>Of the behavior, and not of the helper the search is written in. A filter applies its
 * closure to every candidate on every run, and a search applies its own until one holds: the third
 * candidate's bound is a line the filter draws, and one the search of every candidate never
 * reaches, since the two before it both fail only where the given number is each of them. The
 * behavior's obligations are read in the regions every line on their axis leaves, the helper's
 * among them, so they are read alike where the helper draws the same lines. Nor are the
 * applications a reading was read on the same: they are the applications of the closures written,
 * which are not the same closures.
 */
class ASearchOverWhatAFilterKeptIsReadAsTheSearchOfEveryCandidateTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** One search written two ways: over every candidate, and over what filters kept. */
    private record Written(String everyCandidate, String whatAFilterKept) {}

    /** Over two candidates, the second of which the search reaches wherever the first fails. */
    private static final Written OF_TWO = new Written("""
            List.find(d -> Int.floorMod(d, 7) >= 1 && Int.floorMod(d, 7) <= 5
                    && Bool.not(d == h), List.map(k -> base + k, [0, 1]))""", """
            List.find(d -> Bool.not(d == h), List.filter(d -> Int.floorMod(d, 7) >= 1
                    && Int.floorMod(d, 7) <= 5, List.map(k -> base + k, [0, 1])))""");

    /** Over three, the third of which the search never reaches. */
    private static final Written OF_THREE = new Written("""
            List.find(d -> Int.floorMod(d, 7) >= 1 && Int.floorMod(d, 7) <= 5
                    && Bool.not(d == h), List.map(k -> base + k, [0, 1, 2]))""", """
            List.find(d -> Bool.not(d == h), List.filter(d -> Int.floorMod(d, 7) >= 1
                    && Int.floorMod(d, 7) <= 5, List.map(k -> base + k, [0, 1, 2])))""");

    /** Each candidate kept by two filters, one of each bound. */
    private static final Written THROUGH_TWO_FILTERS = new Written(OF_TWO.everyCandidate(), """
            List.find(d -> Bool.not(d == h), List.filter(d -> Int.floorMod(d, 7) <= 5,
                    List.filter(d -> Int.floorMod(d, 7) >= 1, List.map(k -> base + k, [0, 1]))))""");

    /** Kept by a statement that is not read: a remainder by a number of the input. */
    private static final Written KEPT_BY_WHAT_IS_NOT_READ = new Written("""
            List.find(d -> Int.floorMod(d, h) == 0 && Bool.not(d == h),
                    List.map(k -> base + k, [0, 1]))""", """
            List.find(d -> Bool.not(d == h), List.filter(d -> Int.floorMod(d, h) == 0,
                    List.map(k -> base + k, [0, 1])))""");

    /** The rule compares a value of what was found, held in a field of a record built of it. */
    private static final String ITS_WEEKDAY_IN_A_RECORD = """
            {
                let v = V { nominal = base, landed = first(base, h) }
                Bool.not(Int.floorMod(v.landed, 7) >= 1 && Int.floorMod(v.landed, 7) <= 5)
            }""";

    /** The same value, of what was found itself. */
    private static final String ITS_WEEKDAY = """
            Bool.not(Int.floorMod(first(base, h), 7) >= 1
                    && Int.floorMod(first(base, h), 7) <= 5)""";

    /** What was found, against a constant. */
    private static final String WHAT_WAS_FOUND = "first(base, h) > 2";

    /** Each model measured once, however many of the tests ask its report. */
    private static final Map<String, JsonNode> PARTITIONS = new HashMap<>();

    /** The model, compiled and nothing asked of it yet. */
    private static Compilation compiled(String search, String rule) {
        String source = """
                module demo exposing (g, V)

                data V = { nominal: Int, landed: Int }

                let first (base: Int, h: Int): Int = Option.withDefault(base, SEARCH)

                behavior g : (base: Int, h: Int) -> Bool
                let g (base, h) = RULE
                """.replace("SEARCH", search.indent(4).strip())
                .replace("RULE", rule.indent(4).strip());
        return Compilation.ofSource(source, "Main");
    }

    /** What the body of {@code g} states, as the reading of it concludes. */
    private static Proposition stated(Compilation compilation) {
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        assertNotNull(checked, "the model compiles");
        AnalysisBody analysis = checked.analysisBodies().get("g");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("g");
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        return Pullback.ofATruth(Core.withoutStanding(analysis.core()), reads,
                inputs.reading(rules), Optional.empty()).proposition();
    }

    /** Each line of {@code stated}, with how many ways of choosing each case it decides in has. */
    private static List<String> casesOfEachLine(Proposition stated) {
        List<String> out = new ArrayList<>();
        for (WhereEachLineDecides.Decides line : WhereEachLineDecides.in(stated)) {
            List<BigInteger> ways = new ArrayList<>();
            for (DecidingCase one : line.cases()) {
                ways.add(one.standsFor().structuralWays(BigInteger.TWO.pow(64)));
            }
            out.add(line.line() + " " + ways);
        }
        return out;
    }

    /** The partition the report says of {@code g}, the model measured for its report alone. */
    private static JsonNode partition(String search, String rule) {
        return PARTITIONS.computeIfAbsent(search + "\n" + rule, _ -> {
            Compilation compilation = compiled(search, rule);
            compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors(), search + " " + rule);
            return JSON.readTree(AdequacyReport.of(compilation)
                    .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)))
                    .path("modules").get(0).path("behaviors").get(0).path("partition");
        });
    }

    private static String ruleOf(JsonNode rule) {
        return rule.path("definition").asString() + "#" + rule.path("ordinal").asString();
    }

    /**
     * What each rule of {@code g} leaves at each position, by its place in the body: every line it
     * draws there and every word it is told there.
     */
    private static Map<String, Map<String, Set<String>>> leftAtEachPosition(JsonNode partition) {
        Map<String, Map<String, Set<String>>> byRule = new TreeMap<>();
        for (JsonNode boundary : partition.path("boundaries")) {
            JsonNode target = boundary.path("lineId").path("target");
            for (JsonNode term : target.path("quantity").path("terms")) {
                ofARuleOfG(byRule, boundary.path("lineId").path("line").path("which").path("rule"),
                        term.path("term").path("position").asString())
                        .add("draws " + target + " " + boundary.path("kind").asString());
            }
        }
        for (JsonNode each : partition.path("notRead")) {
            ofARuleOfG(byRule, each.path("ruleId"), each.path("position").asString())
                    .add(each.path("reason").asString());
        }
        return byRule;
    }

    /** Where what a rule leaves at {@code position} is gathered, or nowhere for a rule of the
     *  helper. */
    private static Set<String> ofARuleOfG(Map<String, Map<String, Set<String>>> byRule,
                                          JsonNode rule, String position) {
        String which = ruleOf(rule);
        return which.startsWith("g#")
                ? byRule.computeIfAbsent(which, _ -> new TreeMap<>())
                        .computeIfAbsent(position, _ -> new TreeSet<>())
                : new TreeSet<>();
    }

    /** Every line a rule of the helper draws, whichever rule draws it. */
    private static Set<String> drawnByTheHelper(JsonNode partition) {
        Set<String> out = new TreeSet<>();
        for (JsonNode boundary : partition.path("boundaries")) {
            if (!ruleOf(boundary.path("lineId").path("line").path("which").path("rule"))
                    .startsWith("g#")) {
                out.add(boundary.path("lineId").path("target") + " "
                        + boundary.path("kind").asString());
            }
        }
        return out;
    }

    /**
     * The readings of each obligation of a rule of {@code g}, each without the applications it was
     * read on. An obligation is told by its rule's place in the body, its point and relation, and
     * the line's facts: what the line went through to get there passes through the helper.
     */
    private static Map<String, List<String>> readingsOfEachObligation(JsonNode partition) {
        Map<String, List<String>> out = new TreeMap<>();
        for (JsonNode obligation : partition.path("obligations")) {
            String rule = ruleOf(obligation.path("ruleId"));
            if (!rule.startsWith("g#")) {
                continue;
            }
            JsonNode line = obligation.path("obligationId").path("line");
            String key = rule + " " + obligation.path("point") + " "
                    + obligation.path("relation") + " " + line.path("facts") + " "
                    + obligation.path("obligationId").path("location");
            List<String> readings = out.computeIfAbsent(key, _ -> new ArrayList<>());
            for (JsonNode reading : obligation.path("readings")) {
                ObjectNode alone = (ObjectNode) reading.deepCopy();
                alone.remove("applications");
                readings.add(alone.toString());
            }
            readings.sort(null);
        }
        return out;
    }

    private static void sameStatement(Written search, String rule) {
        Proposition everyCandidate = stated(compiled(search.everyCandidate(), rule));
        Proposition whatAFilterKept = stated(compiled(search.whatAFilterKept(), rule));
        assertEquals(everyCandidate, whatAFilterKept, search + " " + rule);
        assertEquals(casesOfEachLine(everyCandidate), casesOfEachLine(whatAFilterKept),
                search + " " + rule);
    }

    /** Whatever the rule reads of what was found: itself, a remainder of it, or a field of a
     *  record built of it. */
    @Test
    void theTwoSearchesStateOneStatementTakenApartIntoTheSameCases() {
        for (String rule : List.of(ITS_WEEKDAY_IN_A_RECORD, ITS_WEEKDAY, WHAT_WAS_FOUND)) {
            sameStatement(OF_TWO, rule);
        }
    }

    /** A candidate kept by several filters is kept by each; one kept by what is not read is kept
     *  by a statement that says so. */
    @Test
    void soThroughTwoFiltersAndWhereWhatAFilterKeepsByIsNotRead() {
        sameStatement(THROUGH_TWO_FILTERS, ITS_WEEKDAY);
        sameStatement(KEPT_BY_WHAT_IS_NOT_READ, ITS_WEEKDAY);
    }

    /**
     * A rule on what was found leaves every position the same lines and words, and, the helper
     * drawing the same lines either way, its obligations are read alike: of the two rules that
     * were left without lines, one on a remainder of what was found and one on itself.
     */
    @Test
    void aRuleOnWhatWasFoundLeavesEveryPositionWhatItLeftSearchingEveryCandidate() {
        for (String rule : List.of(ITS_WEEKDAY, WHAT_WAS_FOUND)) {
            JsonNode everyCandidate = partition(OF_TWO.everyCandidate(), rule);
            JsonNode whatAFilterKept = partition(OF_TWO.whatAFilterKept(), rule);
            Map<String, Map<String, Set<String>>> left = leftAtEachPosition(whatAFilterKept);
            assertTrue(left.values().stream().flatMap(each -> each.values().stream())
                    .flatMap(Set::stream).anyMatch(each -> each.startsWith("draws ")),
                    "the rule draws lines: " + left);
            assertEquals(leftAtEachPosition(everyCandidate), left, rule);

            assertEquals(drawnByTheHelper(everyCandidate), drawnByTheHelper(whatAFilterKept),
                    "over two candidates the search reaches the second: " + rule);
            Map<String, List<String>> readings = readingsOfEachObligation(whatAFilterKept);
            assertFalse(readings.isEmpty(), "the behavior's obligations are read: " + rule);
            assertEquals(readingsOfEachObligation(everyCandidate), readings, rule);
        }
    }

    /**
     * An obligation is read in the regions every line on its axis leaves, the helper's among them,
     * and over three candidates the filter draws a line the search never reaches.
     */
    @Test
    void overThreeTheFilterDrawsTheThirdCandidatesBoundAndTheSearchDoesNot() {
        Set<String> searched = drawnByTheHelper(partition(OF_THREE.everyCandidate(),
                WHAT_WAS_FOUND));
        Set<String> filtered = drawnByTheHelper(partition(OF_THREE.whatAFilterKept(),
                WHAT_WAS_FOUND));
        assertTrue(filtered.containsAll(searched) && filtered.size() > searched.size(),
                searched + " " + filtered);
    }
}
