package souther.compiler.report;

import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.InteractionRequirements;
import souther.compiler.partition.ObligationIdentity;
import souther.compiler.query.About;
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
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A line about a combination of a body's decisions says which combination it is, and the one it
 * says is the one the line is about.
 *
 * <p>Two questions, checked apart. Whether each condition said is the place a run of the
 * combination is recorded at — every step of the copy it stands in included — is checked against
 * the claims the measure holds the combination to, read here without the reading's own walk. And
 * whether two combinations a page names read as two is checked on the page itself. The first does
 * not give the second: a condition of a combination can be a case of a position, which no claim
 * names, and the page is what has to tell such combinations apart.
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
     * Each condition under a line is a place a run of that combination is recorded at, with every
     * step of the copy it stands in, and the alternatives under it are the ways the measure holds
     * it to that no other way is inside.
     */
    @ParameterizedTest
    @ValueSource(strings = {"MEETING", "TWICE", "NESTED", "NAMED", "SAME_CASES", "OPERATION",
            "MEETS_TWICE", "KEPT"})
    void eachConditionSaidIsAPlaceTheCombinationIsRecordedAt(String fixture) {
        Compilation compilation = measured(FIXTURES.get(fixture));
        AdequacyReport.BehaviorReport behavior =
                AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
        Set<ObligationIdentity.OfACombinationOfDecisions> about = aboutOf(behavior);
        assertTrue(about.size() >= 3, () -> "lines about combinations: " + about);

        for (ObligationIdentity.OfACombinationOfDecisions combination : about) {
            Set<Set<List<Object>>> asked = new HashSet<>();
            for (InteractionRequirements.Way way : waysOf(behavior, combination)) {
                Set<List<Object>> claimed = new HashSet<>();
                for (ControlClaim claim : way.claims()) {
                    claimed.add(claimed(compilation, claim));
                }
                asked.add(claimed);
            }
            Set<Set<List<Object>>> alternatives = new HashSet<>();
            for (Set<List<Object>> way : asked) {
                if (asked.stream().noneMatch(other -> other != way && way.containsAll(other))) {
                    alternatives.add(way);
                }
            }
            Set<Set<List<Object>>> said = new HashSet<>();
            for (List<AdequacyReport.ShownCondition> way : behavior.waysOf(combination)) {
                List<List<Object>> read = way.stream()
                        .map(ALineAboutACombinationSaysWhichCombinationItIsTest::read).toList();
                assertEquals(read.size(), new HashSet<>(read).size(),
                        () -> "no condition said twice in one way: " + read);
                said.add(new HashSet<>(read));
            }
            assertEquals(alternatives, said, () -> "what is said under " + combination);
        }
    }

    /** Every combination a page names reads as its own, and only the ways the page needs are said
     *  as alternatives. */
    @ParameterizedTest
    @ValueSource(strings = {"MEETING", "TWICE", "NESTED", "NAMED", "SAME_CASES", "OPERATION",
            "MEETS_TWICE", "KEPT"})
    void combinationsAPageNamesReadApart(String fixture) {
        Compilation compilation = measured(FIXTURES.get(fixture));
        AdequacyReport report = AdequacyReport.of(compilation);
        Set<ObligationIdentity.OfACombinationOfDecisions> about =
                aboutOf(report.modules().getFirst().behaviors().getFirst());
        List<Set<String>> blocks =
                blocksOf(report.human(SourceRendering.namedByIdentity(compilation.texts())));
        assertEquals(about.size(), blocks.size(), () -> "a line per combination: " + blocks);
        assertEquals(blocks.size(), new HashSet<>(blocks).size(),
                () -> "and no two alike: " + blocks);
    }

    /**
     * Where a combination has more than one way, the page writes one line for it and says the
     * ways under it as alternatives, leaving out a way that has another inside it. The document
     * names the combination once whatever its ways.
     */
    @Test
    void waysAreSaidAsAlternativesUnderOneLine() {
        Compilation compilation = measured(MEETS_TWICE);
        AdequacyReport report = AdequacyReport.of(compilation);
        AdequacyReport.BehaviorReport behavior = report.modules().getFirst().behaviors().getFirst();
        Set<ObligationIdentity.OfACombinationOfDecisions> about = aboutOf(behavior);
        for (ObligationIdentity.OfACombinationOfDecisions combination : about) {
            assertEquals(3, waysOf(behavior, combination).size(),
                    () -> "the meeting in each call and the one between them: " + combination);
            assertEquals(2, behavior.waysOf(combination).size(),
                    () -> "the one between them holds both of the others: " + combination);
        }
        String page = report.human(SourceRendering.namedByIdentity(compilation.texts()));
        assertEquals(about.size(), blocksOf(page).size(), page);
        assertEquals(about.size(), linesSaying(page, "either"), page);
        assertEquals(about.size(), linesSaying(page, "or"), page);

        JsonNode interaction = JsonMapper.builder().build().readTree(
                report.json(SourceRendering.namedByIdentity(compilation.texts())))
                .findValue("interaction");
        int unmade = 0;
        for (JsonNode each : interaction.get("obligations")) {
            unmade += each.get("made").asBoolean() ? 0 : 1;
        }
        assertEquals(about.size(), unmade, () -> "one obligation per line: " + interaction);
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
        List<AdequacyReport.ShownCondition> way =
                behavior.waysOf(aboutOf(behavior).iterator().next()).getFirst();
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

    private static List<InteractionRequirements.Way> waysOf(
            AdequacyReport.BehaviorReport behavior,
            ObligationIdentity.OfACombinationOfDecisions combination) {
        if (!(behavior.evidence().combinations() instanceof CombinationCriterion.Interactions(
                var meetings))) {
            return fail("held to the combinations of its decisions: " + behavior.name());
        }
        return meetings.asked().ways().get(combination);
    }

    /** The combinations a line under {@code behavior} is about. */
    private static Set<ObligationIdentity.OfACombinationOfDecisions> aboutOf(
            AdequacyReport.BehaviorReport behavior) {
        Set<ObligationIdentity.OfACombinationOfDecisions> out = new LinkedHashSet<>();
        for (AdequacyReport.ReportedFinding each : behavior.reported()) {
            if (each.finding().about() instanceof About.ACombinationNoRowMakes(var combination)) {
                out.add(combination);
            }
        }
        for (CoveredOnlyByRowsThatDoNotHold.Covered<ObligationIdentity.OfACombinationOfDecisions>
                each : CoveredOnlyByRowsThatDoNotHold.combinationsOf(
                        behavior.evidence().combinations())) {
            out.add(each.obligation());
        }
        return out;
    }

    /** The lines a page writes under each line about a combination, in no order. */
    private static List<Set<String>> blocksOf(String page) {
        List<Set<String>> out = new ArrayList<>();
        Set<String> block = null;
        for (String line : page.lines().toList()) {
            if (line.contains("this combination of the decisions")) {
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
