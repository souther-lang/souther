package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.LabeledRegion;
import souther.compiler.diag.Severity;
import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReads;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.GenerationOutcome;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way through a body every run of which stops at a construction is a finding a build refuses
 * over: an obligation, established by its proof, told under its own code as a warning, which no
 * row answers. The warning names the behavior and marks the construction where it is written.
 *
 * <p>Read at its owner, under the rules of declarations whose invariant the way's conditions
 * contradict, because every compiled model where this happens is refused by the check of its body
 * (E2010).
 */
class AWayEveryRunOfWhichStopsIsAGapABuildIsWarnedOfTest {

    private static final String BODIES = """
            module demo

            data Positive = { n: Int }
                invariant n >= 1

            data No

            behavior one : (n: Int) -> Positive | No
                constructs Positive
            let one (n) = if n > 5 then Positive { n = n } else No
            """;

    private static final String RULES = """
            module demo

            data Positive = { n: Int }
                invariant n < 0

            data No
            """;

    @Test
    void theWayIsAGapNoRowAnswers() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        Adequacy.Finding finding = findingOf(bodies);

        assertEquals(Adequacy.Kind.WAY_EVERY_RUN_STOPS, finding.kind());
        assertEquals("E1941", finding.code().orElseThrow().toString());
        assertEquals(Severity.WARNING, finding.code().orElseThrow().severity());
        assertTrue(finding.isAdequacyGap(), "a build refuses over it");
        assertInstanceOf(GenerationOutcome.NotApplicable.class,
                Adequacy.whereNoRowCouldAnswer(finding.about()), "and no row answers it");
    }

    @Test
    void theWarningNamesTheBehaviorAndMarksTheConstruction() {
        Compilation bodies = Compilation.ofSource(BODIES, "Main");
        Diagnostic said = Adequacy.Warnings.warning(bodies.db(), "demo", findingOf(bodies),
                new HashMap<>()).diagnostic();

        assertEquals("E1941", said.code());
        assertEquals(new ExampleMessage.EveryRunAlongAWayStopsAtAConstruction("one"), said.said());
        assertEquals(1, said.secondary().size(), () -> "one mark: " + said.secondary());
        LabeledRegion mark = said.secondary().getFirst();
        assertEquals(new ExampleMessage.EveryRunAlongTheWayStopsHere(), mark.said());
        DiagnosticPlace.InSource in = assertInstanceOf(DiagnosticPlace.InSource.class,
                mark.place());
        int at = BODIES.indexOf("Positive { n = n }");
        assertEquals(BODIES.substring(0, at).chars().filter(c -> c == '\n').count() + 1,
                bodies.texts().resolve(in.region().start()).line(),
                "the mark is at the construction");
    }

    /** The finding the account makes of the way into the construction, read under {@link #RULES}. */
    private static Adequacy.Finding findingOf(Compilation bodies) {
        Bodies.Elaborated checked = bodies.db().ask(new Bodies.Checked("demo")).value();
        assertEquals(List.of(), bodies.errors(), "the model the body is read off compiles");
        RuleReadingSource rules = RuleReadings.of(Compilation.ofSource(RULES, "Main"), "demo");
        Map<String, InputDomain> inputs = bodies.db().ask(new Adequacy.Inputs("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("one");
        InputDomain domain = inputs.get("one");
        DecisionReading read = DecisionReading.of("one", analysis, domain.reading(rules),
                InputReads.ofParametersWhereCallsStand(domain.parameterReads(),
                        domain.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                        domain.dependencies()));
        assertEquals(1, read.everyRunStops().size(), () -> "the way into the construction: "
                + read.everyRunStops());
        DecisionReading.EveryRunStops way = read.everyRunStops().getFirst();
        return Adequacy.Finding.noticed("one", new About.AWayEveryRunOfWhichStops("one", way,
                Adequacy.whereRunsStopAt(bodies.db(), way.stoppedAt())));
    }
}
