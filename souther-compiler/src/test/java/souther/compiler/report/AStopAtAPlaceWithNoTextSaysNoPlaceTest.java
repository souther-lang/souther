package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.DocumentShape;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceRendering;
import souther.compiler.execute.RunStop;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.PassedConstruction;
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
import java.util.Locale;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction or an {@code unreachable} whose place has no text is said with no place: the stop
 * holds none, the page names none, and the document writes no {@code module}, {@code sourceId},
 * {@code line} or {@code column} for it — never another module in its stead.
 *
 * <p>No compiled model puts a construction at no place, so the stop is made at its owner
 * ({@link Adequacy#whereRunsStopAt}) from the constructions of a real way with their place taken
 * off, and the page and the document are driven from it as
 * {@link AWayEveryRunOfWhichStopsIsSaidAndOwedNothingTest} drives them.
 */
class AStopAtAPlaceWithNoTextSaysNoPlaceTest {

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
    void aConstructionWithNoPlaceIsStoppedAtWithNoSite() {
        Compilation bodies = compiled();
        List<WhereARunStopped> stops = Adequacy.whereRunsStopAt(bodies.db(),
                placeless(theWay(bodies).stoppedAt()));

        assertEquals(List.of(new WhereARunStopped(new RunStop.AtAConstruction("demo", "Positive",
                Optional.empty(), 0, Optional.empty()), Optional.empty())), stops);
    }

    @Test
    void aStopWithNoSiteIsSaidWithNoPlace() {
        SourceRendering rendering = SourceRendering.namedByIdentity(compiled().texts());

        assertEquals("the runs stopped at the construction, where invariant Positive #1 did not"
                        + " hold and at an `unreachable` (never this)",
                InEnglish.said(GeneratedRows.stoppedAt(List.of(
                        new WhereARunStopped(new RunStop.AtAConstruction("demo", "Positive",
                                Optional.empty(), 0, Optional.empty()), Optional.empty()),
                        new WhereARunStopped(new RunStop.AtAnUnreachable("never this",
                                Optional.empty()), Optional.empty())),
                        InEnglish.page(rendering))));
    }

    @Test
    void aStopIsSaidInTheLanguageOfThePage() {
        Page japanese = new Page(SourceRendering.namedByIdentity(compiled().texts()),
                Locale.JAPANESE);
        List<WhereARunStopped> stops = List.of(
                new WhereARunStopped(new RunStop.AtAConstruction("demo", "Positive",
                        Optional.empty(), 0, Optional.empty()), Optional.empty()),
                new WhereARunStopped(new RunStop.AtAnUnreachable("never this",
                        Optional.empty()), Optional.empty()));

        String said = japanese.say(GeneratedRows.stoppedAt(stops, japanese));

        assertTrue(!said.contains("the runs stopped") && !said.contains("did not hold"),
                () -> "the sentence is in English: " + said);
        // What is a name or what the runtime said is not translated.
        assertTrue(said.contains("Positive") && said.contains("never this"), said);
    }

    @Test
    void theDocumentWritesNoPlaceForAStopWithNone() {
        Compilation bodies = compiled();
        AdequacyReport own = AdequacyReport.of(bodies);
        DecisionReading read = readUnderTheOtherRules(bodies);
        DecisionReading.EveryRunStops way = read.everyRunStops().getFirst();
        List<WhereARunStopped> stops = Adequacy.whereRunsStopAt(bodies.db(),
                placeless(way.stoppedAt()));
        AdequacyReport stopping = withTheWay(bodies, own, read, way, stops);
        SourceRendering rendering = SourceRendering.namedByIdentity(bodies.texts());

        JsonNode document = JSON.readTree(stopping.json(rendering));
        DocumentShape.assertShapedLikeTheSchema(document);
        JsonNode entry = behaviorOf(document, "one").path("decision").path("waysEveryRunStops")
                .path(0);
        assertEquals(JSON.readTree("""
                        [{"at": "a_construction", "rule": "invariant Positive #1",
                          "declaredIn": "demo"}]"""),
                entry.path("runsStopped"));

        String human = stopping.humanInEnglish(rendering);
        assertTrue(human.lines().anyMatch(line -> line.equals("      · every run along a way"
                        + " through this body stops: the runs stopped at the construction, where"
                        + " invariant Positive #1 did not hold")),
                () -> "the page names no place: " + human);
    }

    private static Compilation compiled() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        bodies.measure(Adequacy.Asked.fullReport());
        return ACompiledModel.compiles(bodies);
    }

    private static DecisionReading.EveryRunStops theWay(Compilation bodies) {
        DecisionReading read = readUnderTheOtherRules(bodies);
        assertEquals(1, read.everyRunStops().size(), () -> "the way into the construction: "
                + read.excluded());
        return read.everyRunStops().getFirst();
    }

    /** {@code passed}, each with no place: a construction the code it stands in was made with no
     *  place for. */
    private static List<PassedConstruction> placeless(List<PassedConstruction> passed) {
        return passed.stream()
                .map(each -> new PassedConstruction(each.states(), null, each.clause())).toList();
    }

    /** {@code own}, with the reading of `one` made under {@link #RULES} and {@code stops} as where
     *  the runs along {@code way} stop. */
    private static AdequacyReport withTheWay(Compilation bodies, AdequacyReport own,
                                             DecisionReading read,
                                             DecisionReading.EveryRunStops way,
                                             List<WhereARunStopped> stops) {
        List<AdequacyReport.ModuleReport> modules = new ArrayList<>();
        for (AdequacyReport.ModuleReport module : own.modules()) {
            List<AdequacyReport.BehaviorReport> behaviors = new ArrayList<>();
            for (AdequacyReport.BehaviorReport each : module.behaviors()) {
                behaviors.add(each.name().equals("one")
                        ? stopping(bodies, each, read, way, stops) : each);
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
                                                          DecisionReading.EveryRunStops way,
                                                          List<WhereARunStopped> stops) {
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
        Map<DecisionReading.Ruled, List<WhereARunStopped>> wayStops = new HashMap<>(b.wayStops());
        wayStops.put(way.way(), stops);
        return new AdequacyReport.BehaviorReport(b.name(), b.implementation(), evidence,
                b.rowsOwed(), b.claimed(), b.reported(), b.armPlaces(), b.conditionPlaces(),
                b.rulePlaces(), b.partPlaces(), readings, b.ruleSettlements(),
                b.reachShownWrong(), b.combinationReadings(), b.unobserved(), b.rowPlaces(),
                b.weights(), b.rewritePlaces(), wayStops);
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
