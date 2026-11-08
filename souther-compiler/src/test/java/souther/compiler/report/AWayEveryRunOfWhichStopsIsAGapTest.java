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
import souther.compiler.query.About;
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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way through a body every run of which stops at a construction is a gap: the report marks it
 * {@code !}, the document publishes it as a refused finding under its own word and code, joined to
 * the way's entry by what tells the way apart, and the verdict is not satisfied.
 *
 * <p>Every compiled model where this happens that could be written is refused by the check of its
 * body (E2010), so the report is driven from a reading made at its owner: the body of a model the
 * check accepts, read under the rules of declarations of the same names whose invariant the way's
 * conditions contradict, put in place of the behavior's own reading, with the finding the account
 * makes of it. What the report is held to is what it writes of that reading and finding, which is
 * the same whichever model they came from.
 */
class AWayEveryRunOfWhichStopsIsAGapTest {

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
    void theWayIsAGapInTheReportTheDocumentAndTheVerdict() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        bodies.measure(Adequacy.Asked.fullReport());
        bodies.answerEverything();
        assertEquals(List.of(), bodies.errors(), "the model the body is read off compiles");
        AdequacyReport own = AdequacyReport.of(bodies);
        AdequacyReport stopping = withTheWay(bodies, own);
        SourceRendering rendering = SourceRendering.namedByIdentity(bodies.texts());

        String human = stopping.human(rendering);
        int at = BODIES.indexOf("Positive { n = n }");
        String before = BODIES.substring(0, at);
        String place = (before.chars().filter(c -> c == '\n').count() + 1) + ":"
                + (at - before.lastIndexOf('\n'));
        assertTrue(human.lines().anyMatch(line -> line.startsWith("      ! every run along a way"
                        + " through this body stops: the runs stopped at the construction at ")
                        && line.endsWith(":" + place + ", where invariant Positive #1 did not"
                        + " hold")),
                () -> "the way is marked a gap, with where its runs stop: " + human);

        // The rules of the body under its own declarations are gaps of their own, which no row
        // here takes; the way is one more, and a verdict refuses over it as over them.
        assertEquals(own.adequacyGaps().size() + 1, stopping.adequacyGaps().size());
        assertEquals(List.of(Adequacy.Kind.WAY_EVERY_RUN_STOPS), stopping.adequacyGaps().stream()
                .map(Adequacy.Finding::kind)
                .filter(kind -> kind == Adequacy.Kind.WAY_EVERY_RUN_STOPS).toList());
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED, stopping.adequacy());

        JsonNode document = JSON.readTree(stopping.json(rendering));
        DocumentShape.assertShapedLikeTheSchema(document);
        JsonNode behavior = behaviorOf(document, "one");
        List<JsonNode> found = new ArrayList<>();
        for (JsonNode each : behavior.path("findings")) {
            if (each.path("kind").asString().equals("way_every_run_stops")) {
                found.add(each);
            }
        }
        assertEquals(1, found.size(), () -> "one finding for the way: " + behavior);
        JsonNode finding = found.getFirst();
        assertEquals("refused", finding.path("disposition").asString());
        assertEquals("E1941", finding.path("code").asString());
        JsonNode entry = behavior.path("decision").path("waysEveryRunStops").path(0);
        assertEquals(entry.path("way"), finding.path("obligationId").path("way"),
                "the finding joins the way's entry by the way");
        assertEquals(entry.path("runsStopped"), finding.path("obligationId").path("runsStopped"),
                "and by where its runs stop");
        assertEquals("a_construction",
                entry.path("runsStopped").path(0).path("at").asString());
    }

    /** {@code own}, with the reading of `one` made under {@link #RULES} and the finding the account
     *  makes of the way every run of which stops. */
    private static AdequacyReport withTheWay(Compilation bodies, AdequacyReport own) {
        DecisionReading read = readUnderTheOtherRules(bodies);
        assertEquals(1, read.everyRunStops().size(), () -> "the way into the construction: "
                + read.everyRunStops());
        DecisionReading.EveryRunStops way = read.everyRunStops().getFirst();
        Adequacy.Finding finding = Adequacy.Finding.noticed("one",
                new About.AWayEveryRunOfWhichStops("one", way,
                        Adequacy.whereRunsStopAt(bodies.db(), way.stoppedAt())));
        List<AdequacyReport.ModuleReport> modules = new ArrayList<>();
        for (AdequacyReport.ModuleReport module : own.modules()) {
            List<AdequacyReport.BehaviorReport> behaviors = new ArrayList<>();
            for (AdequacyReport.BehaviorReport each : module.behaviors()) {
                behaviors.add(each.name().equals("one")
                        ? stopping(bodies, each, read, finding) : each);
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
                                                          Adequacy.Finding finding) {
        DecisionEvidence decision = b.evidence().decision();
        BehaviorEvidence e = b.evidence();
        BehaviorEvidence evidence = new BehaviorEvidence(e.reading(), e.signature(),
                e.partition(), e.boundaryReadings(), e.account(), e.branch(),
                new DecisionEvidence(read, decision.took(), decision.unanswered()),
                e.interaction(), e.replacement());
        DecisionReading.EveryRunStops way =
                ((About.AWayEveryRunOfWhichStops) finding.about()).way();
        List<AdequacyReport.ReportedFinding> reported = new ArrayList<>(b.reported());
        reported.add(new AdequacyReport.ReportedFinding(finding,
                Adequacy.placeOf(bodies.db(), "demo", finding), null));
        Map<DecisionReading.Ruled, List<AdequacyReport.ShownCondition>> readings =
                new HashMap<>(b.ruleReadings());
        readings.put(way.way(), AdequacyReport.conditionsOf(bodies.db(), "demo",
                AdequacyReport.placesFor(bodies.db(), "demo", "one"), way.way()));
        Map<DecisionReading.Ruled, List<WhereARunStopped>> stops =
                new HashMap<>(b.wayStops());
        stops.put(way.way(), ((About.AWayEveryRunOfWhichStops) finding.about()).stops());
        return new AdequacyReport.BehaviorReport(b.name(), b.implementation(), evidence,
                b.rowsOwed(), b.claimed(), reported, b.armPlaces(), b.conditionPlaces(),
                b.rulePlaces(), b.partPlaces(), readings, b.ruleSettlements(),
                b.reachShownWrong(), b.combinationReadings(), b.unobserved(), b.rowPlaces(),
                b.weights(), b.rewritePlaces(), stops);
    }

    private static DecisionReading readUnderTheOtherRules(Compilation bodies) {
        RuleReadingSource rules = RuleReadings.of(Compilation.ofSource(RULES, "Main"), "demo");
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
