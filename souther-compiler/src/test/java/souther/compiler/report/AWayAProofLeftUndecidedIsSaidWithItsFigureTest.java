package souther.compiler.report;

import org.junit.jupiter.api.Test;

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
import souther.compiler.query.Weakening;

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
 * document, no finding, and a weakening of the decision's measure that keeps the verdict open under
 * what stopped at a figure.
 *
 * <p>Driven from a reading made at its owner, for the reason
 * {@link AWayEveryRunOfWhichStopsIsAGapTest} is: the body of a model the check accepts, read under
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

    @Test
    void theWayIsSaidUndecidedWithTheFigureInTheReportTheDocumentAndTheVerdict() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        bodies.measure(Adequacy.Asked.fullReport());
        bodies.answerEverything();
        assertEquals(List.of(), bodies.errors(), "the model the body is read off compiles");
        AdequacyReport own = AdequacyReport.of(bodies);
        DecisionReading read = Allowances.DECLARED
                .with(CompositionBudget.CONDITIONS_A_DECISION_TAKES_IN_TO_PROVE, SPENT_AT)
                .over(() -> readUnderTheOtherRules(bodies));
        assertEquals(1, read.undecided().size(), () -> "the way into the constructions: "
                + read.excluded());
        DecisionReading.UndecidedAtAFigure way = read.undecided().getFirst();
        AdequacyReport undecided = withTheWay(bodies, own, read, way);
        SourceRendering rendering = SourceRendering.namedByIdentity(bodies.texts());

        String human = undecided.human(rendering);
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
        assertFalse(human.contains("! every run along a way"), "and is no gap");

        assertTrue(undecided.whatKeepsTheVerdictOpen().stream().anyMatch(each ->
                        each instanceof AdequacyUncertainty.ByWeakening(
                                Weakening.AWayLeftUndecided(var behavior, var left))
                                && behavior.equals("two") && left.equals(way)
                                && each.figures().equals(List.of(FIGURE))
                                && ReaderDisposition.of(each)
                                        instanceof ReaderDisposition.StoppedAtAFigure),
                () -> "the verdict is held open by the way, at the figure: "
                        + undecided.whatKeepsTheVerdictOpen());
        assertEquals(own.heldOpen().atAFigure() + 1, undecided.heldOpen().atAFigure(),
                "counted under what stopped at a figure");
        assertEquals(List.of(), undecided.adequacyGaps(), "and no gap is made of it");
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED, undecided.adequacy());

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
                                             DecisionReading.UndecidedAtAFigure way) {
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
                                                           DecisionReading.UndecidedAtAFigure way) {
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
        stops.put(way.way(), Adequacy.whereRunsStopAt(bodies.db(), way.stoppedAt()));
        return new AdequacyReport.BehaviorReport(b.name(), b.implementation(), evidence,
                b.rowsOwed(), b.claimed(), b.reported(), b.armPlaces(), b.conditionPlaces(),
                b.rulePlaces(), b.partPlaces(), readings, b.ruleSettlements(),
                b.reachShownWrong(), b.combinationReadings(), b.unobserved(), b.rowPlaces(),
                b.weights(), b.rewritePlaces(), stops);
    }

    private static DecisionReading readUnderTheOtherRules(Compilation bodies) {
        RuleReadingSource rules = RuleReadings.of(Compilation.ofSource(RULES, "Main"), "demo");
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
