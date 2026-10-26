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
import souther.compiler.query.InteractionEvidence;
import souther.compiler.query.Sites;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.StepOfACopy;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * What a page and a document say of the combinations no row makes is the choices of the groups of
 * the body's decisions that no row makes, each once, and says which group and which choices.
 *
 * <p>Three questions, checked apart. Whether the sets a report names hold the choices no row makes
 * and nothing else is checked against the group's own account of its choices, not against the
 * report. Whether each condition said is the place a run of the choices is recorded at — every step
 * of the copy it stands in included — is checked against the claims the group holds its choices to,
 * read here without the reading's own walk. And whether the page and the document name the same
 * sets, each joined to the group it is of, is checked on the page and the document themselves.
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

    /** The same, with no row at all: every choice of the one group is missing. */
    private static final String NO_ROWS = KINDS + """
            let f (first, second) = price(first) + price(second)
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

    /** Two groups sharing a decision: both sums take the same call of {@code price} for their
     *  first term, and each has a second term of its own. The sets the two leave missing share the
     *  decision of the shared call and are not the same sets. */
    private static final String SHARED = """
            module p
            data Gold
            data Plain
            data Kind = Gold | Plain
            data Pair = { x: Int, y: Int }
            behavior f : (a: Kind, b: Kind, c: Kind) -> Pair
            let price (kind: Kind): Int =
                match kind with
                    | Gold -> 10
                    | Plain -> 1
            let pair (s: Int, b: Kind, c: Kind): Pair =
                Pair { x = s + price(b), y = s + price(c) }
            let f (a, b, c) = pair(price(a), b, c)
            example f
                | (Gold, Gold, Gold) -> Pair { x = 20, y = 20 }
            """;

    private static final String[] EVERY_FIXTURE = {"MEETING", "TWICE", "NO_ROWS", "NESTED",
            "NAMED", "SAME_CASES", "OPERATION", "MEETS_TWICE", "KEPT", "SHARED"};

    private static final Map<String, String> FIXTURES = Map.of(
            "MEETING", MEETING, "TWICE", TWICE, "NO_ROWS", NO_ROWS, "NESTED", NESTED,
            "NAMED", NAMED, "SAME_CASES", SAME_CASES, "OPERATION", OPERATION,
            "MEETS_TWICE", MEETS_TWICE, "KEPT", KEPT, "SHARED", SHARED);

    /**
     * Each condition under a line, and each one the group is described by, is a place a run of the
     * choices is recorded at, with every step of the copy it stands in: one of the places the group
     * holds its choices to.
     */
    @ParameterizedTest
    @ValueSource(strings = {"MEETING", "TWICE", "NO_ROWS", "NESTED", "NAMED", "SAME_CASES",
            "OPERATION", "MEETS_TWICE", "KEPT", "SHARED"})
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
            group.factors().forEach(factor -> factor.forEach(each -> said.addAll(each.shown())));
            group.choices().forEach(each -> said.addAll(group.fixedConditionsOf(each)));
            for (AdequacyReport.ShownCondition each : said) {
                List<Object> read = read(each);
                assertTrue(places.contains(read), () -> "a place no choice is recorded at: " + read);
            }
        }
    }

    /**
     * The sets of a group hold exactly the choices of it that are combinations no row makes, each
     * once.
     *
     * <p>Checked against the group's own account of its choices and the combinations the rows made,
     * and not against what the report counted: a group that is missing from the report, a set that
     * is missing from a group and a choice in two sets of one group all read differently here.
     */
    @ParameterizedTest
    @ValueSource(strings = {"MEETING", "TWICE", "NO_ROWS", "NESTED", "NAMED", "SAME_CASES",
            "OPERATION", "MEETS_TWICE", "KEPT", "SHARED"})
    void theSetsOfAGroupHoldTheChoicesNoRowMakesOnceEach(String fixture) {
        AdequacyReport.BehaviorReport behavior = behaviorOf(FIXTURES.get(fixture));
        InteractionEvidence meetings = meetingsOf(behavior);
        Set<ObligationIdentity.OfACombinationOfDecisions> made =
                meetings.made().made().orElseThrow().met();
        Map<Integer, AdequacyReport.UnobservedGroup> reported = new HashMap<>();
        behavior.unobserved().forEach(group -> reported.put(group.ordinal(), group));

        List<InteractionRequirements.OfferedGroup> groups = meetings.asked().groups();
        for (int ordinal = 0; ordinal < groups.size(); ordinal++) {
            InteractionRequirements.OfferedGroup offered = groups.get(ordinal);
            Set<Integer> missing = new HashSet<>();
            for (int index = 0; index < offered.at().size(); index++) {
                ObligationIdentity.OfACombinationOfDecisions choice = offered.at().get(index);
                if (choice != null && !made.contains(choice)) {
                    missing.add(index);
                }
            }
            AdequacyReport.UnobservedGroup group = reported.get(ordinal);
            if (missing.isEmpty()) {
                assertNull(group, () -> "a group with nothing missing is not reported");
                continue;
            }
            Set<Integer> held = new HashSet<>();
            for (AdequacyReport.UnobservedChoices pattern : group.choices()) {
                int inIt = 0;
                for (int index = 0; index < offered.at().size(); index++) {
                    if (takes(pattern.fixed(), offered.widths(), index)) {
                        inIt++;
                        int at = index;
                        assertTrue(held.add(index),
                                () -> "a choice in two sets of one group: " + at);
                    }
                }
                assertEquals(inIt, pattern.count(), () -> "what a set says it holds");
            }
            assertEquals(missing, held, () -> "group " + group.ordinal() + " of " + fixture);
        }
    }

    /** Whether the {@code index}th choice of a group takes the outcomes a set names, the first
     *  factor varying fastest. */
    private static boolean takes(List<Integer> fixed, List<Integer> widths, int index) {
        int left = index;
        for (int factor = 0; factor < widths.size(); factor++) {
            int outcome = left % widths.get(factor);
            left /= widths.get(factor);
            if (fixed.get(factor) != null && fixed.get(factor) != outcome) {
                return false;
            }
        }
        return true;
    }

    /**
     * The page and the document name the same sets, and each set the document names is joined to
     * the group it is of by what it takes, which no other set of the document takes.
     */
    @ParameterizedTest
    @ValueSource(strings = {"MEETING", "TWICE", "NO_ROWS", "NESTED", "NAMED", "SAME_CASES",
            "OPERATION", "MEETS_TWICE", "KEPT", "SHARED"})
    void thePageAndTheDocumentNameTheSameSets(String fixture) {
        Compilation compilation = measured(FIXTURES.get(fixture));
        AdequacyReport report = AdequacyReport.of(compilation);
        AdequacyReport.BehaviorReport behavior = report.modules().getFirst().behaviors().getFirst();
        List<AdequacyReport.UnobservedChoices> sets = behavior.unobserved().stream()
                .flatMap(each -> each.choices().stream()).toList();

        String page = report.human(SourceRendering.namedByIdentity(compilation.texts()));
        assertEquals(sets.size(), blocksOf(page).size(), page);

        JsonNode document = JsonMapper.builder().build().readTree(
                report.json(SourceRendering.namedByIdentity(compilation.texts())));
        Map<String, Integer> account = new HashMap<>();
        for (JsonNode group : document.findValue("interaction").get("groups")) {
            for (JsonNode each : group.get("unobserved")) {
                assertNull(account.put(group.get("group").asInt() + "/" + each.get("fixed"),
                        each.get("combinations").asInt()),
                        () -> "no two sets of one group take the same: " + each);
            }
        }
        Set<String> named = new HashSet<>();
        for (JsonNode each : document.findValue("findings")) {
            if (!each.get("kind").asString().equals("interaction_uncovered")) {
                continue;
            }
            JsonNode pattern = each.get("pattern");
            String key = pattern.get("group").asInt() + "/" + pattern.get("fixed");
            assertEquals(account.get(key), each.get("combinations").asInt(),
                    () -> "a finding joins the set of its group: " + each);
            assertTrue(named.add(key), () -> "one finding for a set: " + each);
        }
        assertEquals(account.keySet(), named);
        assertEquals(sets.size(), named.size());
    }

    /**
     * A combination that is alone in its set is a requirement of the body, and the page gives it
     * every way a run can make it, as alternatives.
     *
     * <p>The ways are the combination's and not the set's: a set of several choices has what its
     * outcomes share and no way a single run is held to.
     */
    @Test
    void aCombinationAloneInItsSetKeepsEveryWayToIt() {
        Compilation compilation = measured(MEETS_TWICE);
        AdequacyReport report = AdequacyReport.of(compilation);
        AdequacyReport.BehaviorReport behavior = report.modules().getFirst().behaviors().getFirst();
        int several = 0;
        for (AdequacyReport.UnobservedGroup group : behavior.unobserved()) {
            for (AdequacyReport.UnobservedChoices each : group.choices()) {
                if (each.combination() != null) {
                    assertEquals(3, meetingsOf(behavior).asked().ways().get(each.combination())
                            .size(), "the meeting in each call and the one between them");
                    assertEquals(2, behavior.waysOf(each.combination()).size(),
                            "the one between them holds both of the others");
                    several++;
                }
            }
        }
        assertTrue(several > 0, "a combination alone in its set");
        String page = report.human(SourceRendering.namedByIdentity(compilation.texts()));
        assertEquals(several, linesSaying(page, "either"), page);
        assertEquals(several, linesSaying(page, "or"), page);
    }

    /**
     * Two groups that share a decision are two groups: the sets one leaves missing are not the
     * sets the other does because they take the shared decision alike.
     */
    @Test
    void twoGroupsSharingADecisionAreEachReported() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(SHARED);
        InteractionEvidence meetings = meetingsOf(behavior);
        assertEquals(2, meetings.asked().groups().size(), "a group for each sum");
        assertEquals(2, behavior.unobserved().size(), "and each is missing choices");
        for (AdequacyReport.UnobservedGroup group : behavior.unobserved()) {
            assertEquals(3, group.choices().stream()
                    .mapToInt(AdequacyReport.UnobservedChoices::count).sum(),
                    () -> "all but the one choice a row makes, in group " + group.ordinal());
        }
    }

    /**
     * Where every choice of a group is missing the page still says what the group is made of: each
     * factor and the outcomes it can come out as, once.
     */
    @Test
    void aGroupWithEveryChoiceMissingStillSaysWhatItIsMadeOf() {
        Compilation compilation = measured(NO_ROWS);
        AdequacyReport report = AdequacyReport.of(compilation);
        AdequacyReport.UnobservedGroup group = report.modules().getFirst().behaviors().getFirst()
                .unobserved().getFirst();
        assertEquals(1, group.choices().size(), "every choice in one set");
        assertEquals(4, group.choices().getFirst().count());
        assertTrue(group.choices().getFirst().fixed().stream().allMatch(Objects::isNull),
                "which names no factor");

        String page = report.human(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> lines = page.lines().toList();
        int header = lines.indexOf("      decided together:");
        assertTrue(header >= 0, page);
        assertEquals(2, lines.subList(header + 1, lines.size()).stream()
                .takeWhile(line -> line.startsWith("          · ")).count(),
                () -> "a line for each factor: " + page);
    }

    /**
     * Two combinations of which elements are kept are two entries of the document, whether a row
     * made them or they are among the sets no row makes.
     *
     * <p>The same construct is the decision of each element, so the combinations differ only in
     * which evaluation of it came out which way. A description that left the evaluation out would
     * give the element kept first and the element kept second alike.
     */
    @Test
    void combinationsOfWhichElementsAreKeptAreTheChoicesOfTheDocument() {
        Compilation compilation = measured(KEPT);
        AdequacyReport report = AdequacyReport.of(compilation);
        JsonNode document = JsonMapper.builder().build().readTree(
                report.json(SourceRendering.namedByIdentity(compilation.texts())));

        JsonNode interaction = document.findValue("interaction");
        int choices = interaction.get("obligations").size();
        Set<String> identities = new HashSet<>();
        interaction.get("obligations").forEach(each -> identities.add(
                each.get("obligationId").toString()));
        assertEquals(choices, identities.size(), "no two made combinations under one identity");
        for (JsonNode group : interaction.get("groups")) {
            for (JsonNode each : group.get("unobserved")) {
                choices += each.get("combinations").asInt();
            }
        }
        assertEquals(4, choices, () -> "a combination for each choice: " + interaction);
    }

    /**
     * A set of one choice is the combination of the body that choice is, and the combination is
     * what the group states at that choice.
     */
    @Test
    void aSetOfOneChoiceIsACombinationOfTheBody() {
        AdequacyReport.BehaviorReport behavior = behaviorOf(MEETING);
        var asked = meetingsOf(behavior).asked();
        int alone = 0;
        for (AdequacyReport.UnobservedGroup group : behavior.unobserved()) {
            for (AdequacyReport.UnobservedChoices each : group.choices()) {
                assertEquals(each.count() == 1, each.combination() != null);
                if (each.combination() != null) {
                    alone++;
                    assertTrue(asked.ways().containsKey(each.combination()),
                            () -> "a combination of the body: " + each.combination());
                }
            }
        }
        assertTrue(alone > 0, "a combination alone in its set");
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
        group.choices().forEach(each -> group.fixedConditionsOf(each).stream()
                .filter(condition -> !way.contains(condition)).forEach(way::add));
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

    private static InteractionEvidence meetingsOf(AdequacyReport.BehaviorReport behavior) {
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

    /** How many lines of {@code page} say {@code word} and nothing else. */
    private static long linesSaying(String page, String word) {
        return page.lines().filter(line -> line.strip().equals(word)).count();
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
