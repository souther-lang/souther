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
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.WhereARunStopped;
import souther.compiler.ACompiledModel;
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
 * A way through a body every run of which stops at a construction is said and owed nothing: the
 * report writes it as a {@code ·} line under the decision naming the construction and the clause
 * its runs stop at, the document publishes it under {@code decision.waysEveryRunStops} and as no
 * finding, and the verdict is what it is without it — as for a comparison every run reaching which
 * stops in an operation. What is wrong is the body; the account is a fact about the model by
 * itself, whether or not a check of the model's invariants reports the same construction.
 *
 * <p>The report is driven from a reading made at its owner: the body of a model that compiles, read
 * under the rules of declarations of the same names whose invariant the way's conditions
 * contradict, put in place of the behavior's own reading. What the report is held to is what it
 * writes of that reading, which is the same whichever model it came from.
 */
class AWayEveryRunOfWhichStopsIsSaidAndOwedNothingTest {

    private static final String BODIES = """
            module demo

            data Positive = { n: Int }
                invariant n >= 1

            data No

            behavior one : (n: Int) -> Positive | No
                constructs Positive
            let one (n) = if n > 5 then Positive { n = n } else No
            """;

    /** The same declarations, the first held to what no number past five is. */
    private static final String RULES = """
            module demo

            data Positive = { n: Int }
                invariant n < 0

            data No
            """;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void theWayIsSaidInTheReportAndTheDocumentAndLeavesTheVerdictAsItWas() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        bodies.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(bodies);
        AdequacyReport own = AdequacyReport.of(bodies);
        AdequacyReport stopping = withTheWay(bodies, own);
        SourceRendering rendering = SourceRendering.namedByIdentity(bodies.texts());

        String human = stopping.humanInEnglish(rendering);
        int at = BODIES.indexOf("Positive { n = n }");
        String before = BODIES.substring(0, at);
        String place = (before.chars().filter(c -> c == '\n').count() + 1) + ":"
                + (at - before.lastIndexOf('\n'));
        String demo = rendering.names().nameOf(bodies.sourceIdOf("demo"));
        assertTrue(human.lines().anyMatch(line -> line.equals("      · every run along a way"
                        + " through this body stops: the runs stopped at the construction at "
                        + demo + ":" + place + ", where invariant Positive #1 did not hold")),
                () -> "the way is said, with where its runs stop: " + human);
        assertFalse(human.lines().anyMatch(line -> line.contains("! every run along a way")),
                () -> "and is no gap: " + human);

        assertEquals(own.adequacyGaps(), stopping.adequacyGaps(),
                "the way is no finding a build refuses over");
        assertEquals(own.adequacy(), stopping.adequacy(), "and leaves the verdict as it was");

        JsonNode document = JSON.readTree(stopping.json(rendering));
        DocumentShape.assertShapedLikeTheSchema(document);
        JsonNode behavior = behaviorOf(document, "one");
        assertEquals(behaviorOf(JSON.readTree(own.json(rendering)), "one").path("findings"),
                behavior.path("findings"), "the document carries no finding for the way");
        JsonNode ways = behavior.path("decision").path("waysEveryRunStops");
        assertEquals(1, ways.size(), () -> "one entry for the way: " + behavior);
        JsonNode stopped = ways.path(0).path("runsStopped");
        assertEquals(1, stopped.size(), () -> "one place the runs stop at: " + stopped);
        assertEquals("a_construction", stopped.path(0).path("at").asString());
        assertEquals("invariant Positive #1", stopped.path(0).path("rule").asString());
        assertEquals("demo", stopped.path(0).path("module").asString());
        assertEquals(place, stopped.path(0).path("line").asInt() + ":"
                + stopped.path(0).path("column").asInt());
        assertTrue(ways.path(0).path("way").isObject(), () -> "the way is named: " + ways);
    }

    /** {@code own}, with the reading of `one` made under {@link #RULES} and where the runs along
     *  the way every run of which stops do stop, as the report works it out. */
    private static AdequacyReport withTheWay(Compilation bodies, AdequacyReport own) {
        DecisionReading read = readUnderTheOtherRules(bodies);
        assertEquals(1, read.everyRunStops().size(), () -> "the way into the construction: "
                + read.excluded());
        DecisionReading.EveryRunStops way = read.everyRunStops().getFirst();
        List<AdequacyReport.ModuleReport> modules = new ArrayList<>();
        for (AdequacyReport.ModuleReport module : own.modules()) {
            List<AdequacyReport.BehaviorReport> behaviors = new ArrayList<>();
            for (AdequacyReport.BehaviorReport each : module.behaviors()) {
                behaviors.add(each.name().equals("one")
                        ? stopping(bodies, each, read, way) : each);
            }
            modules.add(new AdequacyReport.ModuleReport(module.module(), module.declaredIn(),
                    behaviors, module.declarations(), module.owedByDeclarations(),
                    module.apart()));
        }
        return new AdequacyReport(own.schemaVersion(), own.compilerVersion(), own.weakenedBy(),
                modules);
    }

    private static AdequacyReport.BehaviorReport stopping(Compilation bodies,
                                                          AdequacyReport.BehaviorReport b,
                                                          DecisionReading read,
                                                          DecisionReading.EveryRunStops way) {
        DecisionEvidence decision = b.evidence().decision();
        BehaviorEvidence e = b.evidence();
        BehaviorEvidence evidence = new BehaviorEvidence(e.reading(), e.signature(),
                e.partition(), e.boundaryReadings(), e.account(), e.branch(),
                new DecisionEvidence(read, decision.took(), decision.unanswered()),
                e.interaction(), e.replacement());
        Map<DecisionReading.Ruled, List<AdequacyReport.ShownCondition>> readings =
                new HashMap<>(b.ruleReadings());
        readings.put(way.way(), AdequacyReport.conditionsOf(bodies.db(), "demo",
                AdequacyReport.placesFor(bodies.db(), "demo", "one"), way.way()));
        Map<DecisionReading.Ruled, List<WhereARunStopped>> stops = new HashMap<>(b.wayStops());
        stops.put(way.way(), Adequacy.whereRunsStopAt(bodies.db(), way.stoppedAt()));
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
        AnalysisBody analysis = checked.analysisBodies().get("one");
        InputDomain domain = inputs.get("one");
        return DecisionReading.of("one", analysis, domain.reading(rules),
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
