package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.DocumentShape;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.observe.Figure;
import souther.compiler.partition.Allowances;
import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.WhereARunStopped;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BehaviorEvidence;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way no input gets past, where the proof stopped at a figure before it could say whether any
 * input takes it, is said as undecided with the figure: a {@code ?} line on the page naming the
 * figure and where the runs along it would stop, an entry of its own under the decision in the
 * document and no finding. It holds no verdict open: no input gets past the constructions on it
 * either way.
 *
 * <p>Driven from a reading made at its owner, for the reason
 * {@link AWayEveryRunOfWhichStopsIsSaidAndOwedNothingTest} is: the body of a model the check accepts, read under
 * the rules of declarations of the same names whose invariant the way's conditions contradict, and
 * held to a figure of conditions taken in small enough to be spent before the proof without the
 * second construction is answered.
 */
class AWayAProofLeftUndecidedIsSaidWithItsFigureTest {

    private static final String BODIES = """
            module demo

            data Positive = { n: Int }
                invariant n >= 1

            data Small = { n: Int }
                invariant n <= 1000

            data No

            behavior two : (n: Int) -> Small | No
                constructs Positive, Small
            let two (n) = if n > 5 then {
                let p = Positive { n = n }
                Small { n = p.n }
            } else No

            example two
                | "low" : (1) -> No
                | "at the line" : (5) -> No
                | "past the line" : (6) -> Small { n = 6 }
                | "high" : (100) -> Small { n = 100 }
            """;

    /** The same declarations, the first held to what no number past five is. */
    private static final String RULES = """
            module demo

            data Positive = { n: Int }
                invariant n < 0

            data Small = { n: Int }
                invariant n <= 1000

            data No
            """;

    /** The figure the proof of the way is held to, which its proof fits in and the proof without
     *  the second construction does not. */
    private static final int SPENT_AT = 8;

    private static final Figure FIGURE = new Figure.Budget(
            CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE, SPENT_AT);

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** The report of the model, and the same with the reading of `two` in place of its own, which
     *  holds a way the proof left undecided. */
    private record Undecided(Compilation bodies, AdequacyReport own, AdequacyReport undecided,
                             DecisionReading.UndecidedAtAFigure way) {}

    private static Undecided undecidedWay() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        bodies.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(bodies);
        AdequacyReport own = AdequacyReport.of(bodies);
        DecisionReading read =Allowances.DECLARED
                .with(CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE, SPENT_AT)
                .over(() -> readUnderTheOtherRules(bodies));
        assertEquals(1, read.undecided().size(), () -> "the way into the constructions: "
                + read.excluded());
        DecisionReading.UndecidedAtAFigure way = read.undecided().getFirst();
        return new Undecided(bodies, own, withTheWay(bodies, own, read, way), way);
    }

    /**
     * The proof that no input both takes the way's conditions and gets past the constructions on
     * it was had in full, so no rule past the way is owed a row whichever way the question left
     * open comes out. The way holds nothing open: a verdict that is satisfied without it is
     * satisfied with it.
     */
    @Test
    void aWayLeftUndecidedDoesNotTurnASatisfiedVerdictUndetermined() {
        Undecided had = undecidedWay();

        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, had.own().adequacy(),
                "the verdict without the way is the one asked to stay");
        assertEquals(AdequacyReport.AdequacyStatus.SATISFIED, had.undecided().adequacy());
        assertEquals(had.own().whatKeepsTheVerdictOpen(),
                had.undecided().whatKeepsTheVerdictOpen(), "the way holds nothing open");
        assertEquals(had.own().heldOpen(), had.undecided().heldOpen(),
                "and is counted under nothing");
        assertEquals(List.of(), had.undecided().adequacyGaps(), "and no gap is made of it");
    }

    /** The reading of `two` under the other rules, held to {@code allowance} conditions taken in. */
    private static DecisionReading readAt(Compilation bodies, int allowance) {
        Compilation held = ACompiledModel.compiles(bodies);
        return Allowances.DECLARED
                .with(CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE, allowance)
                .over(() -> readUnderTheOtherRules(held));
    }

    /**
     * The allowance of conditions taken in is a boundary of the proof and not a mode of it. A
     * proof that takes in as many conditions as the allowance is had in full, and the way is said
     * as the unbounded reading says it; one more condition than the allowance and the proof is cut
     * off, which is said as the way being undecided at the allowance. At no allowance, however
     * small, is a cut-off proof read as a proof of the way: a way not proved is a way kept, and one
     * the proof without a construction was cut short for is undecided, never a way every run of
     * which stops.
     *
     * <p>Across the three allowances around the boundary the rules owed rows and the verdict are
     * the same: a cut-off proof changes what is said of the way and nothing that is owed.
     */
    @Test
    void aProofCutOffAtItsAllowanceIsUndecidedAndNeverAProvenExclusion() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        bodies.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(bodies);
        AdequacyReport own = AdequacyReport.of(bodies);
        DecisionReading unbounded = readUnderTheOtherRules(bodies);
        assertEquals(1, unbounded.everyRunStops().size(), () -> "the proof in full: "
                + unbounded.excluded());

        int needed = 0;
        while (readAt(bodies, needed).everyRunStops().isEmpty()) {
            needed++;
            assertTrue(needed < 64, "the proof is had in full at some small allowance");
        }
        for (int allowance = 0; allowance < needed; allowance++) {
            DecisionReading cut = readAt(bodies, allowance);
            int at = allowance;
            assertEquals(List.of(), cut.impossible(), () -> "at " + at + ": " + cut.excluded());
            assertEquals(List.of(), cut.everyRunStops(), () -> "at " + at + ": " + cut.excluded());
        }

        DecisionReading under = readAt(bodies, needed - 1);
        DecisionReading at = readAt(bodies, needed);
        DecisionReading over = readAt(bodies, needed + 1);
        assertEquals(1, under.undecided().size(), () -> "one condition short: " + under.excluded());
        assertEquals(new Figure.Budget(CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE,
                needed - 1), under.undecided().getFirst().figure());
        assertEquals(unbounded.everyRunStops(), at.everyRunStops(), "as many as it takes");
        assertEquals(List.of(), at.undecided());
        assertEquals(unbounded.everyRunStops(), over.everyRunStops(), "and more");
        assertEquals(List.of(), over.undecided());

        assertEquals(at.found(), under.found(), "the rules owed rows are the same cut off");
        assertEquals(at.found(), over.found());
        JsonNode atDecision = decisionOf(bodies, own, at, at.everyRunStops().getFirst());
        JsonNode underDecision = decisionOf(bodies, own, under, under.undecided().getFirst());
        JsonNode overDecision = decisionOf(bodies, own, over, over.everyRunStops().getFirst());
        for (String said : List.of("obligations", "coverage")) {
            assertEquals(atDecision.path(said), underDecision.path(said), said);
            assertEquals(atDecision.path(said), overDecision.path(said), said);
        }
        assertEquals(withTheWay(bodies, own, at, at.everyRunStops().getFirst()).adequacy(),
                withTheWay(bodies, own, under, under.undecided().getFirst()).adequacy());
        assertEquals(withTheWay(bodies, own, at, at.everyRunStops().getFirst()).adequacy(),
                withTheWay(bodies, own, over, over.everyRunStops().getFirst()).adequacy());
    }

    /** The decision of `two` the document writes, of the report holding {@code read}. */
    private static JsonNode decisionOf(Compilation bodies, AdequacyReport own,
                                       DecisionReading read, DecisionReading.Excluded way) {
        AdequacyReport report = withTheWay(bodies, own, read, way);
        JsonNode document = JSON.readTree(report.json(
                SourceRendering.namedByIdentity(bodies.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        return behaviorOf(document, "two").path("decision");
    }

    @Test
    void theWayIsSaidUndecidedWithTheFigureInTheReportAndTheDocument() {
        Undecided had = undecidedWay();
        Compilation bodies = had.bodies();
        DecisionReading.UndecidedAtAFigure way = had.way();
        AdequacyReport undecided = had.undecided();
        assertEquals(FIGURE, way.figure());
        SourceRendering rendering = SourceRendering.namedByIdentity(bodies.texts());

        String human = undecided.humanInEnglish(rendering);
        String positive = placeOf("Positive { n = n }");
        String demo = rendering.names().nameOf(bodies.sourceIdOf("demo"));
        assertTrue(human.lines().anyMatch(line -> line.startsWith("      ? whether any input takes"
                        + " a way through this body was not decided — stopped at how many"
                        + " conditions are taken in asking whether some input takes a way through"
                        + " one body (CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE, " + SPENT_AT
                        + "), which no option sets; every run along it would stop at the"
                        + " construction at " + demo + ":" + positive
                        + ", where invariant Positive #1 did not hold")),
                () -> "the way is marked undecided, with its figure: " + human);
        assertFalse(human.contains("every run along a way through this body stops"),
                "and is not said to be a way every run of which stops");

        JsonNode document = JSON.readTree(undecided.json(rendering));
        DocumentShape.assertShapedLikeTheSchema(document);
        JsonNode behavior = behaviorOf(document, "two");
        JsonNode entry = behavior.path("decision").path("waysUndecided");        assertEquals(1, entry.size(), () -> "one entry for the way: " + behavior);
        assertEquals(JSON.readTree("[\"conditions_a_decision_takes_in_to_prove\"]"),
                entry.path(0).path("figures"));
        assertEquals("a_construction",
                entry.path(0).path("runsStopped").path(0).path("at").asString());
        assertTrue(behavior.path("decision").path("waysEveryRunStops").isMissingNode());
        assertTrue(behavior.path("decision").path("waysNoInputTakes").isMissingNode());
    }

    /** The line and column {@code text} starts at in {@link #BODIES}. */
    private static String placeOf(String text) {
        int at = BODIES.indexOf(text);
        String before = BODIES.substring(0, at);
        return (before.chars().filter(c -> c == '\n').count() + 1) + ":"
                + (at - before.lastIndexOf('\n'));
    }

    /** {@code own}, with the reading of `two` in place of its own. */
    private static AdequacyReport withTheWay(Compilation bodies, AdequacyReport own,
                                             DecisionReading read,
                                             DecisionReading.Excluded way) {
        List<AdequacyReport.ModuleReport> modules = new ArrayList<>();
        for (AdequacyReport.ModuleReport module : own.modules()) {
            List<AdequacyReport.BehaviorReport> behaviors = new ArrayList<>();
            for (AdequacyReport.BehaviorReport each : module.behaviors()) {
                behaviors.add(each.name().equals("two") ? undecided(bodies, each, read, way)
                        : each);
            }
            modules.add(new AdequacyReport.ModuleReport(module.module(), module.declaredIn(),
                    behaviors, module.declarations(), module.owedByDeclarations(),
                    module.apart()));
        }
        return new AdequacyReport(own.schemaVersion(), own.compilerVersion(), own.weakenedBy(),
                modules);
    }

    private static AdequacyReport.BehaviorReport undecided(Compilation bodies,
                                                           AdequacyReport.BehaviorReport b,
                                                           DecisionReading read,
                                                           DecisionReading.Excluded way) {
        DecisionEvidence decision = b.evidence().decision();
        BehaviorEvidence e = b.evidence();
        BehaviorEvidence evidence = new BehaviorEvidence(e.reading(), e.signature(),
                e.partition(), e.boundaryReadings(), e.account(), e.branch(),
                new DecisionEvidence(read, decision.took(), decision.unanswered()),
                e.interaction(), e.replacement());
        Map<DecisionReading.Ruled, List<AdequacyReport.ShownCondition>> readings =
                new HashMap<>(b.ruleReadings());
        readings.put(way.way(), AdequacyReport.conditionsOf(bodies.db(), "demo",
                AdequacyReport.placesFor(bodies.db(), "demo", "two"), way.way()));
        Map<DecisionReading.Ruled, List<WhereARunStopped>> stops = new HashMap<>(b.wayStops());
        stops.put(way.way(), Adequacy.whereRunsStopAt(bodies.db(), way.way().passed()));
        return new AdequacyReport.BehaviorReport(b.name(), b.implementation(), evidence,
                b.rowsOwed(), b.claimed(), b.reported(), b.armPlaces(), b.conditionPlaces(),
                b.rulePlaces(), b.partPlaces(), readings, b.ruleSettlements(),
                b.reachShownWrong(), b.combinationReadings(), b.unobserved(), b.rowPlaces(),
                b.weights(), b.rewritePlaces(), stops);
    }

    private static DecisionReading readUnderTheOtherRules(Compilation bodies) {
        RuleReadingSource rules = RuleReadings.of(ACompiledModel.answered(RULES), "demo");
        Bodies.Elaborated checked = bodies.db().ask(new Bodies.Checked("demo")).value();
        Map<String, InputDomain> inputs = bodies.db().ask(new Adequacy.Inputs("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("two");
        InputDomain domain = inputs.get("two");
        return DecisionReading.of("two", analysis, domain.reading(rules),
                InputReads.ofParametersWhereCallsStand(domain.parameterReads(),
                        domain.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        domain.dependencies()));
    }

    private static JsonNode behaviorOf(JsonNode document, String name) {
        for (JsonNode module : document.path("modules")) {
            for (JsonNode each : module.path("behaviors")) {
                if (each.path("name").asString().equals(name)) {
                    return each;
                }
            }
        }
        throw new AssertionError("the document says nothing of " + name + ": " + document);
    }
}
