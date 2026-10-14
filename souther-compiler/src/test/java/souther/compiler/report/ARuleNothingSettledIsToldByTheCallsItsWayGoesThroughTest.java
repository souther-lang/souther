package souther.compiler.report;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.ConditionGap;
import souther.compiler.partition.DecisionRule;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.SettledAt;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule of a decision nothing settled is an entry of its own, told by which way each call of a
 * helper went, and what its search went without is said once per thing to say.
 *
 * <p>The model calls one helper three times, and the helper's comparison is one place in the
 * source. So the conditions of a rule are three conditions written at one place, and what tells
 * them apart — and the rules apart — is the call each was copied at. A page that sends a reader to
 * the place alone shows four rules the same way and one condition several times.
 */
class ARuleNothingSettledIsToldByTheCallsItsWayGoesThroughTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module example.draw

            data MB = Int
                invariant value >= 0
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

        assertTrue(unsettled > 1, "the model leaves more than one rule unsettled, which is what"
                + " makes telling them apart the question");
        assertEquals(unsettled, entries(page(compilation)).size(),
                () -> "one entry per rule the document says nothing settled: "
                        + page(compilation));
    }

    @Test
    void theRulesAreToldApartByWhichWayEachCallWent() {
        List<Entry> entries = entries(page(compiled()));
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
        Map<DecisionRule, SettledAt> settled = compilation.db()
                .ask(new Adequacy.DecisionSearch("example.draw", "draw")).value();
        List<SettledAt> unsettled = settled.values().stream()
                .filter(each -> each.settlement().requirement()
                        instanceof RuleRequirement.Unsettled)
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
        for (Entry entry : entries(page(compiled()))) {
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
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
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
