package souther.compiler;

import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.query.Report;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row leaves behind: an observation, whether or not the row held.
 *
 * <p>The evaluation used to answer with failures alone, so a source with one failing row said nothing
 * about the rows around it. Every measure of how well a model is exampled reads these observations, so
 * a failing row has to keep saying which case the behavior actually produced and which inputs were
 * legal — otherwise a real gap and a broken row look the same from above.
 */
class ExampleOutcomeTest {

    private static final String MODEL = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Rejected = { reason: String }

            behavior submit : (request: Draft) -> Submitted | Rejected
                constructs Submitted, Rejected

            let submit (request) = {
                guard request.cost.value <= 100 else Rejected { reason = "over" }
                Submitted { cost = request.cost }
            }
            """;

    private record Evaluated(Output.Examples.Of value, List<Report> reports) {}

    private static Evaluated evaluate(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Output.Examples key = Output.Examples.asked(compilation.db(), module,
                compilation.sourceIds().get(0));
        return new Evaluated(compilation.db().ask(key).value(), compilation.db().ask(key).reports());
    }

    private static RowOutcome onlyRow(Evaluated evaluated) {
        assertNotNull(evaluated.value(), "the answer carries what the rows observed");
        assertEquals(1, evaluated.value().rows().size());
        return evaluated.value().rows().get(0);
    }

    @Test
    void aRowThatHoldsSaysWhatItExpectedAndWhatItSaw() {
        RowOutcome row = onlyRow(evaluate(MODEL + """

                example submit
                    | "within the ceiling" : (Draft { cost = Amount(50) }) -> Submitted
                """));

        assertEquals(Stage.COMPARED, row.stage());
        assertEquals(Disposition.HELD, row.disposition());
        assertEquals(FailurePhase.NONE, row.failurePhase());
        assertEquals("submit", row.target());
        assertEquals(new RowIdentity.Named("within the ceiling"), row.identity());
        assertEquals("Submitted", row.expectedArm().name());
        assertEquals("Submitted", row.resultArm().name());
        assertEquals(List.of("Draft"), row.inputCases().stream().map(t -> t.name()).toList());
    }

    /** The point of keeping both arms: this row is no evidence for {@code Submitted} and is evidence
     * that {@code Rejected} can happen. */
    @Test
    void aRowThatDisagreesStillSawWhatItSaw() {
        Evaluated evaluated = evaluate(MODEL + """

                example submit
                    | "over the ceiling" : (Draft { cost = Amount(500) }) -> Submitted
                """);
        RowOutcome row = onlyRow(evaluated);

        assertTrue(evaluated.reports().stream().anyMatch(r -> "E1905".equals(r.diagnostic().code())),
                "the row is still reported as failing");
        assertEquals(Stage.COMPARED, row.stage());
        assertEquals(Disposition.FAILED, row.disposition());
        assertEquals(FailurePhase.COMPARISON, row.failurePhase());
        assertEquals("Submitted", row.expectedArm().name());
        assertEquals("Rejected", row.resultArm().name());
        assertTrue(row.observed(), "a row that ran is evidence about the case it produced");
    }

    @Test
    void anInputThatBreaksAnInvariantStopsBeforeAnythingIsEstablished() {
        Evaluated evaluated = evaluate(MODEL + """

                example submit
                    | "negative" : (Draft { cost = Amount(-1) }) -> Submitted
                """);
        RowOutcome row = onlyRow(evaluated);

        assertTrue(evaluated.reports().stream().anyMatch(r -> "E1903".equals(r.diagnostic().code())));
        assertEquals(Stage.NONE, row.stage());
        assertEquals(Disposition.FAILED, row.disposition());
        assertEquals(FailurePhase.INPUT_FIXTURE, row.failurePhase());
        assertEquals(List.of(), row.inputs(), "nothing was built, so nothing was observed");
        assertNull(row.resultArm());
        assertFalse(row.observed());
    }

    @Test
    void anExpectationNamingACaseTheBehaviorCannotProduceStopsAtTheExpectation() {
        RowOutcome row = onlyRow(evaluate(MODEL + """

                example submit
                    | "wrong arm" : (Draft { cost = Amount(50) }) -> Draft
                """));

        assertEquals(Stage.NONE, row.stage());
        assertEquals(FailurePhase.EXPECTED_FIXTURE, row.failurePhase());
        assertEquals("Draft", row.expectedArm().name());
    }

    @Test
    void anInputIsObservedAsSomethingTheCompilerOwns() {
        RowOutcome row = onlyRow(evaluate(MODEL + """

                example submit
                    | (Draft { cost = Amount(50) }) -> Submitted
                """));

        ObservedValue.Constructed draft =
                assertInstanceOf(ObservedValue.Constructed.class, row.inputs().get(0));
        assertEquals("Draft", draft.type().name());
        ObservedValue.Constructed amount =
                assertInstanceOf(ObservedValue.Constructed.class, draft.field("cost"));
        assertEquals("Amount", amount.type().name());
        assertEquals(new ObservedValue.Integer(50L), amount.field("value"));
        assertEquals(new RowIdentity.Unnamed(1), row.identity(),
                "a row need not be named, and an unnamed one is shown by which of its behavior's it is");
    }

    /** A position is a line and a column; once rows are gathered under a module it no longer says
     * which file they came from. */
    @Test
    void aRowFromAnAttachedFileNamesThatFile() {
        Map<String, String> documents = new LinkedHashMap<>();
        documents.put("trip.sou", MODEL);
        documents.put("trip-examples.sou", """
                examples for example.trip

                example submit
                    | "attached" : (Draft { cost = Amount(50) }) -> Submitted
                """);
        Compilation compilation = Compilation.ofDocuments(documents, Set.of(),
                souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();

        Output.Examples.Of attached = compilation.db()
                .ask(new Output.Examples("example.trip", new SourceId("trip-examples.sou"), Output.CoverageMode.NONE)).value();
        assertNotNull(attached);
        assertEquals(1, attached.rows().size());
        assertEquals(new SourceId("trip-examples.sou"), attached.rows().get(0).at().sourceId());
        assertEquals(Disposition.HELD, attached.rows().get(0).disposition());

        Output.Examples.Of own = compilation.db()
                .ask(new Output.Examples("example.trip", new SourceId("trip.sou"), Output.CoverageMode.NONE)).value();
        assertNotNull(own);
        assertEquals(List.of(), own.rows(), "the module's own source wrote no rows");
    }

    @Test
    void aDependencyWithNoFakeStopsAfterTheFixturesAreBuilt() {
        RowOutcome row = onlyRow(evaluate("""
                module example.clock

                data Draft = { cost: Int }
                data Submitted = { at: String }

                behavior now : () -> String

                behavior stamp : (d: Draft) -> Submitted
                    depends on now
                    constructs Submitted

                let stamp (d, now) = Submitted { at = now() }

                example stamp
                    | (Draft { cost = 1 }) -> Submitted
                """));

        assertEquals(Stage.FIXTURES_VALIDATED, row.stage());
        assertEquals(Disposition.FAILED, row.disposition());
        assertEquals(FailurePhase.FAKE_RESOLUTION, row.failurePhase());
        assertEquals(1, row.inputs().size(), "the fixtures were built before the fake was wanted");
    }

    @Test
    void anArmDeclaredUnreachableThatIsReachedStopsInsideTheBehavior() {
        RowOutcome row = onlyRow(evaluate("""
                module example.leave

                data UnderThirty
                data ThirtyOrOver
                data AgeBand = UnderThirty | ThirtyOrOver

                data UnderOneYear
                data TwentyYearsOrMore
                data ServiceBand = UnderOneYear | TwentyYearsOrMore

                data Days = Int invariant value >= 90 && value <= 330

                behavior daysFor : (age: AgeBand, service: ServiceBand) -> Days
                    constructs Days

                let daysFor (age, service) =
                    match age with
                        | UnderThirty ->
                            match service with
                                | UnderOneYear      -> Days(90)
                                | TwentyYearsOrMore -> unreachable "cannot precede thirty"
                        | ThirtyOrOver ->
                            match service with
                                | UnderOneYear      -> Days(120)
                                | TwentyYearsOrMore -> Days(240)

                example daysFor
                    | (UnderThirty, TwentyYearsOrMore) -> Days(90)
                """));

        assertEquals(Stage.INVOKED, row.stage());
        assertEquals(Disposition.FAILED, row.disposition());
        assertEquals(FailurePhase.INVOCATION, row.failurePhase());
        assertNull(row.resultArm(), "nothing was answered, so nothing was observed of the output");
    }

    @Test
    void aSourceWithNoRowsObservesNothingAndSaysSo() {
        Evaluated evaluated = evaluate(MODEL);
        assertNotNull(evaluated.value());
        assertEquals(List.of(), evaluated.value().rows());
        assertEquals(List.<Incompleteness>of(), evaluated.value().incompleteness());
    }
}
