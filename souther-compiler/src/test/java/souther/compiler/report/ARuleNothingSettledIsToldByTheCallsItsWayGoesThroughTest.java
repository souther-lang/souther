package souther.compiler.report;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.ConditionGap;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.ReachabilityGap;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSettlement;
import souther.compiler.query.SettledAcross;
import souther.compiler.query.SettledAt;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule of a decision nothing settled is an entry of its own, told by which way each call of a
 * helper went, and what its search went without is said once per thing to say.
 *
 * <p>The model calls one helper three times, and the helper's comparison is one place in the
 * source. So the conditions of a rule are three conditions written at one place, and what tells
 * them apart — and the rules apart — is the call each was copied at. A page that sends a reader to
 * the place alone shows the rules the same way and one condition several times.
 *
 * <p>The amounts carry no bound, so a cap may be below nought and each of the eight ways the three
 * calls can go is some input's: none is closed as a way no input takes, and a row is owed at every
 * rule. What the search for a row finds at each of those is the search's, and a search that finds
 * more is no reason for this page to say less, so the answer at every place is put as unsettled
 * and the page is read for what it says of the model's own rules, the calls and the conditions.
 * Each condition the composing went without is a condition of the way the rule is stated at, and
 * the way is the real one.
 */
class ARuleNothingSettledIsToldByTheCallsItsWayGoesThroughTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module example.draw

            data MB = Int
            data Held = { carried: MB, plan: MB, extra: MB }
            data Drawn = { fromCarried: MB, fromPlan: MB, fromExtra: MB, throttled: MB }

            behavior draw : (used: MB, held: Held) -> Drawn
                constructs Drawn, MB

            let draw (used, held) = {
                let (a, rest1) = take(used, held.carried)
                let (b, rest2) = take(rest1, held.plan)
                let (c, rest3) = take(rest2, held.extra)
                Drawn { fromCarried = a, fromPlan = b, fromExtra = c, throttled = rest3 }
            }

            let take (used: MB, cap: MB): (MB, MB) =
                if used.value <= cap.value then (used, MB(0))
                else (cap, MB(used.value - cap.value))

            let full = Held { carried = MB(100), plan = MB(500), extra = MB(100) }

            example draw
                | "within carried" : (MB(50), full) -> Drawn { fromCarried = MB(50), fromPlan = MB(0), fromExtra = MB(0), throttled = MB(0) }
                | "into plan" : (MB(150), full) -> Drawn { fromCarried = MB(100), fromPlan = MB(50), fromExtra = MB(0), throttled = MB(0) }
                | "into extra" : (MB(650), full) -> Drawn { fromCarried = MB(100), fromPlan = MB(500), fromExtra = MB(50), throttled = MB(0) }
                | "throttled" : (MB(800), full) -> Drawn { fromCarried = MB(100), fromPlan = MB(500), fromExtra = MB(100), throttled = MB(100) }
            """;

    /** One rule's entry on the page: its opening line and the lines under it. */
    private record Entry(String opening, List<String> under) {

        List<String> conditions() {
            return under.stream().filter(line -> line.startsWith("the comparison at ")).toList();
        }

        List<String> leftOut() {
            return under.stream().filter(line -> line.startsWith("not composed against: "))
                    .map(line -> line.substring("not composed against: ".length())).toList();
        }
    }

    @Test
    void everyRuleNothingSettledIsAnEntryOfItsOwn() {
        Compilation compilation = compiled();
        long unsettled = 0;
        for (JsonNode rule : JSON.readTree(json(compilation)).get("modules").get(0)
                .get("behaviors").get(0).get("decision").get("obligations")) {
            if (rule.get("requirement") != null
                    && "unsettled".equals(rule.get("requirement").stringValue())) {
                unsettled++;
            }
        }

        assertEquals(settledAcross(compilation).size(), unsettled,
                "the document says of every rule the search was put to that nothing settled it");
        assertTrue(unsettled > 1, "the model leaves more than one rule unsettled, which is what"
                + " makes telling them apart the question");
        assertEquals(unsettled, entries(page(compilation)).size(),
                () -> "one entry per rule the document says nothing settled: "
                        + page(compilation));
    }

    /**
     * Along the ways a rule is stated at, those whose numbers contradict each other are no ways,
     * and the search for a row looks along the ones left. A row is found at every rule the
     * examples leave untaken, which looked along the way whole was not.
     */
    @Test
    void aRowIsFoundAtEveryRuleTheExamplesLeaveUntaken() {
        Map<DecisionRule, SettledAcross> searched = compiled().db()
                .ask(new Adequacy.DecisionSearch("example.draw", "draw")).value();

        assertFalse(searched.isEmpty(), "the examples leave rules untaken");
        searched.forEach((rule, across) -> assertInstanceOf(RuleRequirement.Required.class,
                across.requirement(), () -> "a row is owed at " + rule + ": " + across));
    }

    @Test
    void theRulesAreToldApartByWhichWayEachCallWent() {
        List<Entry> entries = entries(page(compiled()));
        assertFalse(entries.isEmpty(), "there are rules nothing settled to tell apart");
        Set<List<String>> told = new HashSet<>();
        for (Entry entry : entries) {
            assertEquals(callsOfTake(), callsNamedIn(entry.conditions()),
                    () -> "every condition of the rule names the call it is in: " + entry);
            told.add(entry.conditions());
        }
        assertEquals(entries.size(), told.size(),
                () -> "no two rules are described alike: " + entries);
    }

    @Test
    void whatASearchWentWithoutIsSaidOnceForEachThingToSay() {
        Compilation compilation = compiled();
        Map<DecisionRule, SettledAcross> settled = settledAcross(compilation);
        // An entry per place each rule nothing settled is stated at.
        List<SettledAt> unsettled = settled.values().stream()
                .filter(each -> each.requirement() instanceof RuleRequirement.Unsettled)
                .flatMap(each -> each.places().stream())
                .toList();
        List<Entry> entries = entries(page(compilation));
        assertEquals(unsettled.size(), entries.size());
        boolean someGapCameBackMoreThanOnce = false;
        for (Entry entry : entries) {
            assertEquals(new LinkedHashSet<>(entry.leftOut()).size(), entry.leftOut().size(),
                    () -> "nothing is said twice under one rule: " + entry);
        }
        for (SettledAt each : unsettled) {
            List<ConditionGap> gaps = each.leftOut();
            Set<String> reasons = new LinkedHashSet<>();
            gaps.forEach(gap -> reasons.add(AdequacyReport.whyLeftOut(gap)));
            someGapCameBackMoreThanOnce |= reasons.size() < gaps.size();
            // Every reason the search came back with is said under some entry, so nothing was
            // dropped in saying each once.
            for (String reason : reasons) {
                assertTrue(entries.stream().anyMatch(entry -> entry.leftOut().stream()
                                .anyMatch(line -> line.startsWith(reason))),
                        () -> "`" + reason + "` is said: " + entries);
            }
        }
        assertTrue(someGapCameBackMoreThanOnce, "the model is one whose searches come back with"
                + " a reason more than once, which is what saying it once is about");
    }

    @Test
    void aConditionLeftOutIsPlacedAtTheCallsItWasMetIn() {
        List<Entry> entries = entries(page(compiled()));
        assertTrue(entries.stream().anyMatch(entry -> !entry.leftOut().isEmpty()),
                "some entry says what its composing went without");
        for (Entry entry : entries) {
            for (String line : entry.leftOut()) {
                Set<String> named = callsNamedIn(List.of(line));
                assertFalse(named.isEmpty(),
                        () -> "a condition of the helper names a call of it: " + line);
                assertTrue(callsOfTake().containsAll(named),
                        () -> "and only calls the body wrote: " + line);
            }
        }
    }

    /** Where the body calls {@code take}, as the page writes a place, read off the model's text. */
    private static Set<String> callsOfTake() {
        Set<String> out = new LinkedHashSet<>();
        List<String> lines = MODEL.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            int at = lines.get(i).indexOf("= take(");
            if (at >= 0) {
                out.add("take@" + (i + 1) + ":" + (at + "= ".length() + 1));
            }
        }
        assertEquals(3, out.size(), "the body calls the helper three times");
        return out;
    }

    /** Every call a line names, in the page's spelling. */
    private static Set<String> callsNamedIn(List<String> lines) {
        Set<String> out = new LinkedHashSet<>();
        for (String line : lines) {
            Matcher call = Pattern.compile("take@\\d+:\\d+").matcher(line);
            while (call.find()) {
                out.add(call.group());
            }
        }
        return out;
    }

    /** The entries of rules nothing settled, in the decision measure of the page. */
    private static List<Entry> entries(String page) {
        List<Entry> out = new ArrayList<>();
        String opening = null;
        List<String> under = new ArrayList<>();
        boolean inDecision = false;
        for (String line : page.split("\n")) {
            if (line.startsWith("    ") && !line.startsWith("      ")) {
                inDecision = line.startsWith("    decision ");
            }
            if (!inDecision) {
                continue;
            }
            if (line.startsWith("      ? ")) {
                if (opening != null) {
                    out.add(new Entry(opening, List.copyOf(under)));
                }
                opening = line.strip();
                under = new ArrayList<>();
            } else if (opening != null && line.startsWith("          · ")) {
                under.add(line.substring("          · ".length()));
            } else if (opening != null) {
                out.add(new Entry(opening, List.copyOf(under)));
                opening = null;
            }
        }
        if (opening != null) {
            out.add(new Entry(opening, List.copyOf(under)));
        }
        return out;
    }

    private static String page(Compilation compilation) {
        return reported(compilation).human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String json(Compilation compilation) {
        return reported(compilation).json(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /**
     * What the search came to at each place of each rule the rows left untaken, with the answer
     * put as one that composed a row short of the way, having left out every condition of the way
     * for one reason. A reason the conditions of one helper share is the same sentence at each,
     * which is what the page says once.
     *
     * <p>Made up, and not what a search came to: no search says this of these rules, which is the
     * point. The places and their ways are the compiled ones, and the answer is put so that the
     * page is read for what it says of them whatever a search finds.
     */
    private static Map<DecisionRule, SettledAcross> settledAcross(Compilation compilation) {
        Map<DecisionRule, SettledAcross> searched = compilation.db()
                .ask(new Adequacy.DecisionSearch("example.draw", "draw")).value();
        assertFalse(searched.isEmpty(), "the rows leave rules untaken, which are searched");
        Map<DecisionRule, SettledAcross> out = new LinkedHashMap<>();
        searched.forEach((rule, across) -> out.put(rule, new SettledAcross(
                across.places().stream().map(ARuleNothingSettledIsToldByTheCallsItsWayGoesThroughTest
                        ::unsettledAt).toList())));
        return out;
    }

    private static SettledAt unsettledAt(SettledAt came) {
        List<ReachabilityGap> gaps = new ArrayList<>();
        for (OnTheWay each : came.at().states().onTheWay()) {
            switch (each) {
                case OnTheWay.TakenIn taken -> gaps.add(new ReachabilityGap.Uncomposed(taken,
                        new ReachabilityGap.Why.NoValueComposedForItsPositions()));
                case OnTheWay.OneOf several -> gaps.add(new ReachabilityGap.LookedAlongWhole(
                        several, CompositionBudget.WAYS_A_WAY_IS_LOOKED_ALONG));
                case OnTheWay.Settled _, OnTheWay.Narrowed _, OnTheWay.Declined _ -> { }
            }
        }
        return new SettledAt(came.at(), RuleSettlement.of(
                new RuleRequirement.Unsettled.AComposedRowWasShortOfTheWay(),
                CompositionAccount.ofTheInput(gaps)), Set.of());
    }

    /** The report of the compilation, with the search put as {@link #settledAcross}. */
    private static AdequacyReport reported(Compilation compilation) {
        AdequacyReport real = AdequacyReport.of(compilation);
        Map<DecisionRule, SettledAcross> unsettled = settledAcross(compilation);
        List<AdequacyReport.ModuleReport> modules = new ArrayList<>();
        for (AdequacyReport.ModuleReport module : real.modules()) {
            List<AdequacyReport.BehaviorReport> behaviors = new ArrayList<>();
            for (AdequacyReport.BehaviorReport each : module.behaviors()) {
                behaviors.add(new AdequacyReport.BehaviorReport(each.name(), each.implementation(),
                        each.evidence(), each.rowsOwed(), each.claimed(), each.reported(),
                        each.armPlaces(), each.conditionPlaces(), each.rulePlaces(),
                        each.partPlaces(), each.ruleReadings(), unsettled, each.reachShownWrong(),
                        each.combinationReadings(), each.rowPlaces()));
            }
            modules.add(new AdequacyReport.ModuleReport(module.module(), module.declaredIn(),
                    behaviors, module.declarations(), module.owedByDeclarations()));
        }
        return new AdequacyReport(real.schemaVersion(), real.compilerVersion(), real.weakenedBy(),
                modules);
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return compilation;
    }
}
