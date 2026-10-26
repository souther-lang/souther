package souther.compiler.report;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.InteractionRequirements;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.CombinationCriterion;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionRuleReading;
import souther.compiler.query.Sites;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.StepOfACopy;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A line about the combinations no row makes says which of them it is about, and what it says is
 * what the group of the body's decisions holds.
 *
 * <p>Two questions, checked apart. Whether each condition said is the place a run of the choices is
 * recorded at — every step of the copy it stands in included — is checked against the claims the
 * group holds its choices to, read here without the reading's own walk. And whether the patterns a
 * page names are the choices no row makes, once each, is checked on the page and the document.
 */
class ALineAboutACombinationSaysWhichCombinationItIsTest {

    /** Two decisions meeting at one value, six combinations: two no row makes, and one only the
     *  row that does not hold makes. */
    private static final String MEETING = """
            module example.meeting

            data Total = Int
            data Premium
            data Standard
            data Membership = Premium | Standard
            data Express
            data Regular
            data Delivery = Express | Regular
            data Fee = Int

            behavior shippingFee : (total: Total, member: Membership, delivery: Delivery) -> Fee
                constructs Fee

            let shippingFee (total, member, delivery) =
                Fee(baseFee(total, member) + expressFee(delivery))

            let baseFee (total: Total, member: Membership): Int =
                match member with
                    | Premium -> 0
                    | Standard -> if total.value >= 5000 then 0 else 500

            let expressFee (delivery: Delivery): Int =
                match delivery with
                    | Express -> 500
                    | Regular -> 0

            example shippingFee
                | (Total(0), Premium, Express)     -> Fee(500)
                | (Total(0), Standard, Regular)    -> Fee(500)
                | (Total(5000), Premium, Regular)  -> Fee(0)
                | (Total(5000), Standard, Express) -> Fee(1)
            """;

    private static final String KINDS = """
            module p
            data Gold
            data Plain
            data Kind = Gold | Plain
            behavior f : (first: Kind, second: Kind) -> Int
            let price (kind: Kind): Int =
                match kind with
                    | Gold -> 10
                    | Plain -> 1
            """;

    /** One value called on both inputs: the decisions are one construct in two calls. */
    private static final String TWICE = KINDS + """
            let f (first, second) = price(first) + price(second)
            example f
                | (Gold, Gold) -> 20
            """;

    /** One value called inside another called twice: two steps to each decision. */
    private static final String NESTED = KINDS + """
            let outer (k: Kind): Int = price(k)
            let f (first, second) = outer(first) + outer(second)
            example f
                | (Gold, Gold) -> 20
            """;

    /** A value passed by name to one that applies it, twice. */
    private static final String NAMED = KINDS + """
            let apply (g: (Kind) -> Int, k: Kind): Int = g(k)
            let f (first, second) = apply(price, first) + apply(price, second)
            example f
                | (Gold, Gold) -> 20
            """;

    /** Two positions matched on the same cases, where the body itself writes both. */
    private static final String SAME_CASES = """
            module p
            data Gold
            data Plain
            data Kind = Gold | Plain
            behavior f : (first: Kind, second: Kind) -> Int
            let f (first, second) =
                (match first with
                    | Gold -> 10
                    | Plain -> 1)
                + (match second with
                    | Gold -> 10
                    | Plain -> 1)
            example f
                | (Gold, Gold) -> 20
            """;

    /** One of the language's own operations called on both inputs: the decisions are inside its
     *  code, one construct in two calls. */
    private static final String OPERATION = """
            module p
            data H = { a: Option<Int>, b: Option<Int> }
            behavior f : (h: H) -> Int
            let f (h) = Option.withDefault(0, h.a) + Option.withDefault(0, h.b)
            example f
                | (H { a = 1, b = 2 }) -> 3
            """;

    /** The same two decisions meet at a value of a helper and again where two calls of it meet,
     *  so each combination has more than one way. */
    private static final String MEETS_TWICE = KINDS + """
            let both (a: Kind, b: Kind): Int = price(a) * price(b)
            let f (first, second) = both(first, second) + both(first, second)
            example f
                | (Gold, Gold) -> 200
            """;

    /** One comparison applied to each of two elements: the same construct is a decision per
     *  element, and the combinations differ in which element a way is said of. */
    private static final String KEPT = """
            module p
            data Row = { days: Int, pay: Int }
            behavior total : (first: Row, second: Row) -> Int
            let total (first, second) =
                List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ first, second ])))
            example total
                | (Row { days = 20, pay = 100 }, Row { days = 5, pay = 200 }) -> 100
            """;

    private static final Map<String, String> FIXTURES = Map.of(
            "MEETING", MEETING, "TWICE", TWICE, "NESTED", NESTED, "NAMED", NAMED,
            "SAME_CASES", SAME_CASES, "OPERATION", OPERATION, "MEETS_TWICE", MEETS_TWICE,
            "KEPT", KEPT);

    /**
     * Each condition under a line is a place a run of the choices is recorded at, with every step
     * of the copy it stands in: one of the places the group holds its choices to.
     */
    @ParameterizedTest
    @ValueSource(strings = {"MEETING", "TWICE", "NESTED", "NAMED", "SAME_CASES", "OPERATION",
            "MEETS_TWICE", "KEPT"})
    void eachConditionSaidIsAPlaceTheChoicesAreRecordedAt(String fixture) {
        Compilation compilation = measured(FIXTURES.get(fixture));
        AdequacyReport.BehaviorReport behavior =
                AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
        assertTrue(!behavior.unobserved().isEmpty(), () -> "choices no row makes: " + fixture);

        Set<List<Object>> places = new HashSet<>();
        for (InteractionRequirements.OfferedGroup offered : meetingsOf(behavior).asked().groups()) {
            offered.reach().claims().forEach(claim -> places.add(claimed(compilation, claim)));
            for (List<InteractionRequirements.Outcome> factor : offered.byFactor()) {
                for (InteractionRequirements.Outcome outcome : factor) {
                    outcome.claims().forEach(claim -> places.add(claimed(compilation, claim)));
                }
            }
        }
        for (AdequacyReport.UnobservedGroup group : behavior.unobserved()) {
            List<AdequacyReport.ShownCondition> said = new ArrayList<>(group.wayIn());
            group.choices().forEach(each -> said.addAll(each.decided()));
            for (AdequacyReport.ShownCondition each : said) {
                List<Object> read = read(each);
                assertTrue(places.contains(read), () -> "a place no choice is recorded at: " + read);
            }
        }
    }

    /**
     * The patterns of a group hold each choice no row makes once: their counts add up to the
     * combinations the rows did not make, and a group that several groups arrive at is not counted
     * in each.
     */
    @ParameterizedTest
    @ValueSource(strings = {"MEETING", "TWICE", "NESTED", "NAMED", "SAME_CASES", "OPERATION",
            "MEETS_TWICE", "KEPT"})
    void thePatternsHoldTheCombinationsNoRowMakesOnceEach(String fixture) {
        AdequacyReport.BehaviorReport behavior = behaviorOf(FIXTURES.get(fixture));
        var meetings = meetingsOf(behavior);
        Set<ObligationIdentity.OfACombinationOfDecisions> missing = new HashSet<>();
        Set<ObligationIdentity.OfACombinationOfDecisions> made =
                meetings.made().made().orElseThrow().met();
        for (ObligationIdentity.OfACombinationOfDecisions each : meetings.asked().ways().keySet()) {
            if (!made.contains(each)) {
                missing.add(each);
            }
        }
        int held = behavior.unobserved().stream().flatMap(each -> each.choices().stream())
                .mapToInt(AdequacyReport.UnobservedChoices::count).sum();
        assertTrue(held >= missing.size(),
                () -> held + " choices in the patterns, " + missing.size() + " combinations");
        if (meetings.asked().groups().size() == 1) {
            assertEquals(missing.size(), held, () -> "one group, so each combination once");
        }
    }

    /** Every pattern a page names is a line, and the document has the same patterns as findings
     *  with the same counts. */
    @ParameterizedTest
    @ValueSource(strings = {"MEETING", "TWICE", "NESTED", "NAMED", "SAME_CASES", "OPERATION",
            "MEETS_TWICE", "KEPT"})
    void thePageAndTheDocumentNameTheSamePatterns(String fixture) {
        Compilation compilation = measured(FIXTURES.get(fixture));
        AdequacyReport report = AdequacyReport.of(compilation);
        AdequacyReport.BehaviorReport behavior = report.modules().getFirst().behaviors().getFirst();
        List<AdequacyReport.UnobservedChoices> patterns = behavior.unobserved().stream()
                .flatMap(each -> each.choices().stream()).toList();

        String page = report.human(SourceRendering.namedByIdentity(compilation.texts()));
        assertEquals(patterns.size(), blocksOf(page).size(), page);

        JsonNode document = JsonMapper.builder().build().readTree(
                report.json(SourceRendering.namedByIdentity(compilation.texts())));
        List<Integer> counted = new ArrayList<>();
        Set<String> identities = new HashSet<>();
        for (JsonNode each : document.findValue("findings")) {
            if (each.get("kind").asString().equals("interaction_uncovered")) {
                counted.add(each.get("combinations").asInt());
                identities.add(each.get("obligationId").toString());
            }
        }
        assertEquals(patterns.stream().map(AdequacyReport.UnobservedChoices::count).toList(),
                counted);
        assertEquals(counted.size(), identities.size(), () -> "no two under one identity");
    }

    /**
     * Two combinations of which elements are kept are two identities in the document, whether they
     * are made or stated as missing.
     *
     * <p>The same construct is the decision of each element, so the combinations differ only in
     * which evaluation of it came out which way. An identity that left the evaluation out would be
     * one for the element kept first and the element kept second alike.
     */
    @Test
    void combinationsOfWhichElementsAreKeptAreTwoIdentitiesInTheDocument() {
        Compilation compilation = measured(KEPT);
        AdequacyReport report = AdequacyReport.of(compilation);
        JsonNode document = JsonMapper.builder().build().readTree(
                report.json(SourceRendering.namedByIdentity(compilation.texts())));

        List<String> identities = new ArrayList<>();
        int choices = 0;
        for (JsonNode each : document.findValue("interaction").get("obligations")) {
            identities.add(each.get("obligationId").toString());
            choices += each.has("combinations") ? each.get("combinations").asInt() : 1;
        }
        assertEquals(4, choices, () -> "a combination for each choice: " + identities);
        assertEquals(identities.size(), new HashSet<>(identities).size(),
                () -> "and no two under one identity: " + identities);
        for (JsonNode each : document.findValue("findings")) {
            if (each.get("kind").asString().equals("interaction_uncovered")) {
                assertTrue(identities.contains(each.get("obligationId").toString()),
                        () -> "a finding joins an entry: " + each);
            }
        }
    }

    /**
     * A pattern of one choice names every decision of the combination, so its identity is the one
     * the combination had; a pattern of more names fewer.
     */
    @Test
    void aPatternOfOneChoiceHasTheIdentityOfTheCombination() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MEETING);
        var meetings = meetingsOf(behavior);
        Set<Set<?>> combinations = new HashSet<>();
        meetings.asked().ways().keySet().forEach(each -> combinations.add(each.settled()));
        for (AdequacyReport.UnobservedGroup group : behavior.unobserved()) {
            for (AdequacyReport.UnobservedChoices each : group.choices()) {
                if (each.count() == 1) {
                    assertTrue(combinations.contains(each.settled()),
                            () -> "a combination of the body: " + each.settled());
                }
            }
        }
    }

    /**
     * An arm inside one of the language's own operations, called twice, is shown where its own
     * call reached it: the first call's arms at the first call, the second's at the second.
     *
     * <p>Read off the page and held to where the fixture writes the two calls, so a page that sent
     * the second call's arm to the first — the place the arm's site was made for — reads wrong
     * here whatever the reading it was handed said.
     */
    @Test
    void anArmInsideAnOperationIsShownWhereItsOwnCallReachedIt() {
        String written = OPERATION.lines().filter(line -> line.startsWith("let f")).findFirst()
                .orElseThrow();
        int line = OPERATION.lines().toList().indexOf(written) + 1;
        int first = written.indexOf("Option.withDefault") + 1;
        int second = written.indexOf("Option.withDefault", first) + 1;
        Set<String> calls = Set.of(line + ":" + first, line + ":" + second);

        Compilation compilation = measured(OPERATION);
        String page = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Pattern arm = Pattern.compile("reached at (\\d+:\\d+)\\) in withDefault@(\\d+:\\d+)");
        Set<String> shown = new HashSet<>();
        for (Set<String> block : blocksOf(page)) {
            for (String condition : block) {
                Matcher said = arm.matcher(condition);
                assertTrue(said.find(), () -> "an arm said with its call: " + condition);
                assertEquals(said.group(2), said.group(1),
                        () -> "shown where its own call reached it: " + condition);
                shown.add(said.group(1));
            }
        }
        assertEquals(calls, shown, () -> "each call's arms at that call: " + page);
    }

    /** Two ways naming the same conditions in two orders are said once, in the first one's order. */
    @Test
    void aWayThatReadsLikeAnEarlierOneIsSaidOnce() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MEETING);
        AdequacyReport.UnobservedGroup group = behavior.unobserved().getFirst();
        List<AdequacyReport.ShownCondition> way = new ArrayList<>(group.wayIn());
        way.addAll(group.choices().getFirst().decided());
        assertTrue(way.size() > 1, () -> "a way of more than one condition: " + way);

        assertEquals(List.of(way), AdequacyReport.distinctWays(List.of(way, way.reversed())));
        assertEquals(List.of(way.reversed()),
                AdequacyReport.distinctWays(List.of(way.reversed(), way)));
    }

    /** What a claim is recorded at: which construct, which way, where it is shown, and every step
     *  of its copy — read off the claim's occurrence by a walk of this test's own. */
    private static List<Object> claimed(Compilation compilation, ControlClaim claim) {
        return switch (claim.at()) {
            // And where a page sends a reader for the arm, which is where the claim is recorded:
            // asked of the claim's own anchor and set beside what the page was handed, so a page
            // that resolved the arm's place from anything else is caught here.
            case ControlPlace.Arm(var arm, var _, var anchor) ->
                    List.of("arm", arm.origin(), arm.part(), anchor,
                            Sites.placeOf(compilation.db(), anchor), steps(arm.fork().lineage()));
            case ControlPlace.Outcome(var occurrence, var _, var held) ->
                    claim.visit() instanceof ControlClaim.Visit.Nth(int index)
                            ? List.of("evaluation", occurrence.origin(), index, held,
                                    steps(occurrence.lineage()))
                            : List.of("outcome", occurrence.origin(), held,
                                    steps(occurrence.lineage()));
        };
    }

    /** The same, read off what a page was handed: the one copy a combination's condition is of,
     *  whose calls the page holds innermost first. */
    private static List<Object> read(AdequacyReport.ShownCondition shown) {
        assertTrue(shown.through().size() <= 1, () -> "one copy of each condition: " + shown);
        List<StepOfACopy> through = shown.through().isEmpty() ? List.of()
                : shown.through().getFirst().stream().map(AdequacyReport.CallSite::step).toList()
                        .reversed();
        return switch (shown.read()) {
            case DecisionRuleReading.AForkTookAnArm(var arm, var shownAt) ->
                    List.of("arm", arm.obligation().origin(), arm.obligation().part(), shownAt,
                            shown.at(), steps(through));
            case DecisionRuleReading.AComparisonCameOut(var comparison, var evaluation, var held) ->
                    evaluation.isPresent()
                            ? List.of("evaluation", comparison.obligation().origin(),
                                    evaluation.getAsInt(), held, steps(through))
                            : List.of("outcome", comparison.obligation().origin(), held,
                                    steps(through));
            case DecisionRuleReading.AnApplicationAnswered(var application, var held) ->
                    List.of("outcome", application.application().origin(), held, steps(through));
            case DecisionRuleReading.AConditionIsNotShown _, DecisionRuleReading.AnOutcomeIsNotPlaced _,
                 DecisionRuleReading.AForkIsNotPlaced _ ->
                    fail("every condition of these fixtures has a site: " + shown);
        };
    }

    private static List<List<Object>> steps(OccurrenceLineage lineage) {
        List<List<Object>> out = new ArrayList<>();
        OccurrenceLineage at = lineage;
        while (!(at instanceof OccurrenceLineage.Original)) {
            if (at instanceof OccurrenceLineage.Expansion copy) {
                out.addFirst(List.of("call", copy.expanded(), copy.at()));
                at = copy.within();
            } else if (at instanceof OccurrenceLineage.Materialisation build) {
                out.addFirst(List.of("build", build.materialised(), build.at()));
                at = build.within();
            }
        }
        return out;
    }

    private static List<List<Object>> steps(List<StepOfACopy> through) {
        return through.stream().map(step -> switch (step) {
            case StepOfACopy.ACall(var called, var at) -> List.<Object>of("call", called, at);
            case StepOfACopy.ABuild(var built, var at) -> List.<Object>of("build", built, at);
        }).toList();
    }

    private static souther.compiler.query.InteractionEvidence meetingsOf(
            AdequacyReport.BehaviorReport behavior) {
        if (!(behavior.evidence().combinations() instanceof CombinationCriterion.Interactions(
                var meetings))) {
            return fail("held to the combinations of its decisions: " + behavior.name());
        }
        return meetings;
    }

    /** The lines a page writes under each line about missing combinations, in no order. */
    private static List<Set<String>> blocksOf(String page) {
        List<Set<String>> out = new ArrayList<>();
        Set<String> block = null;
        for (String line : page.lines().toList()) {
            if (line.contains("no row makes this combination of the decisions")
                    || line.contains("no row makes any of these")) {
                block = new HashSet<>();
                out.add(block);
            } else if (block != null && line.startsWith("          ")) {
                block.add(line.strip());
            } else {
                block = null;
            }
        }
        return out;
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String source) {
        return AdequacyReport.of(measured(source)).modules().getFirst().behaviors().getFirst();
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
