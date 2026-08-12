package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How well the rows cover a model is a different question from whether the model compiles, and
 * {@code souther examples} answers the first one.
 *
 * <p>The specification says so — "Nothing here changes what compiles; it reports" — and the command
 * read it one way round only. It took its compilation from the entry point a batch compile uses,
 * which raises the first error it finds, so every failure the report exists to describe stopped the
 * report from being written at all.
 */
class ACompilationThatFailedStillReportsWhatItsRowsCoverTest {

    /** One behavior that checks and one that does not, so there is something to report and a reason
     * the command still refuses. */
    private static final String ONE_BEHAVIOR_DOES_NOT_CHECK = """
            module example.partly

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Draft = { cost: Amount }
            data Ok = { n: Int }
            data Refused = { why: String }

            behavior take : (request: Draft) -> Ok | Refused
                constructs Ok

            let take (request) = Ok { n = request.cost.value }

            behavior other : (request: Draft) -> Ok
                constructs Ok

            let other (request) = Ok { n = request.cost.nope }

            example take
                | (Draft { cost = Amount(7) }) -> Ok { n = 7 }
            """;

    /** A module, and an attached file declaring a value the module already declares — so the rows in
     * the attached file are never evaluated and nothing knows what they covered. */
    private static final String MODULE_WITH_A_SHARED_VALUE = """
            module example.split

            data Amount = Int
                invariant value >= 0 && value <= 1000

            data Draft = { cost: Amount }
            data Ok = { n: Int }

            let shared = Draft { cost = Amount(7) }

            behavior take : (request: Draft) -> Ok
                constructs Ok

            let take (request) = Ok { n = request.cost.value }

            example take
                | (Draft { cost = Amount(7) }) -> Ok { n = 7 }
            """;

    private static final String ATTACHED_DECLARING_IT_AGAIN = """
            examples for example.split

            let shared = Draft { cost = Amount(0) }

            example take
                | (Draft { cost = Amount(0) }) -> Ok { n = 0 }
            """;

    /** Two behaviors, each reading a field its input has not got: two problems, neither behind the
     * other. */
    private static final String TWO_BEHAVIORS_DO_NOT_CHECK = """
            module example.twice

            data Draft = { cost: Int }
            data Ok = { n: Int }

            behavior take : (request: Draft) -> Ok
                constructs Ok

            let take (request) = Ok { n = request.nope }

            behavior other : (request: Draft) -> Ok
                constructs Ok

            let other (request) = Ok { n = request.alsoNope }
            """;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private record Streams(int code, String out, String err) {}

    private static Streams run(String source, String... extraArgs) throws Exception {
        return ran(List.of(source), extraArgs);
    }

    /** The module and its attached file, given to the command together as an author gives them. */
    private static Streams runBoth(String... extraArgs) throws Exception {
        return ran(List.of(MODULE_WITH_A_SHARED_VALUE, ATTACHED_DECLARING_IT_AGAIN), extraArgs);
    }

    private static Streams ran(List<String> texts, String... extraArgs) throws Exception {
        Path dir = Files.createTempDirectory("souther-examples");
        List<String> args = new ArrayList<>(List.of("examples"));
        args.addAll(List.of(extraArgs));
        for (int i = 0; i < texts.size(); i++) {
            Path file = dir.resolve(i == 0 ? "model.sou" : "attached" + i + ".sou");
            Files.writeString(file, texts.get(i));
            args.add(file.toString());
        }

        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            // `dispatch` rather than `main`, which turns a non-zero answer into a dead JVM.
            code = Main.dispatch(args.toArray(String[]::new));
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
        return new Streams(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }

    @Test
    void theReportIsWrittenForAModuleOneOfWhoseBehaviorsDidNotCheck() throws Exception {
        Streams ran = run(ONE_BEHAVIOR_DOES_NOT_CHECK, "--format", "json");

        assertFalse(ran.out().isBlank(),
                "the report is what this command answers with; stderr said: " + ran.err());
        JsonNode report = JSON.readTree(ran.out());
        assertEquals("example.partly", report.get("modules").get(0).get("module").asString(),
                "the module is there to be reported on, whatever else did not check");
    }

    @Test
    void theDiagnosticIsStillSaidAndTheCommandStillRefuses() throws Exception {
        Streams ran = run(ONE_BEHAVIOR_DOES_NOT_CHECK, "--format", "json");

        assertEquals(1, ran.code(), "a compilation with an error is still a failed command");
        assertTrue(ran.err().contains("E1321"),
                "the diagnostic goes where it always went: " + ran.err());
    }

    /**
     * And the field that says what the assessment did without is finally written.
     *
     * <p>The whole of {@code incompleteness} was unreachable: all but one of the reasons it carries
     * arrive with a diagnostic beside them — the exception is the runtime not being reachable — so a
     * report only a clean compile produced could carry almost nothing the field is for. Here a
     * source declares a value the module already declares, so its rows are never evaluated and
     * whatever they covered is unknown.
     *
     * <p>The word is not asserted. Which code a source that produced no observation should carry is
     * its own question, and this test is about the entry existing at all.
     */
    @Test
    void aSourceThatWasNeverEvaluatedIsSaidToBeMissingFromTheAssessment() throws Exception {
        Streams ran = runBoth("--format", "json");

        assertEquals(1, ran.code());
        JsonNode gaps = JSON.readTree(ran.out()).get("modules").get(0).get("incompleteness");
        assertEquals(1, gaps.size(), "the attached source went unread: " + ran.out());
        assertEquals("source", gaps.get(0).get("scope").asString(),
                "what could not be read is the source, so it counts against everything in it");
    }

    /**
     * Every error, where the raising entry point said the first one.
     *
     * <p>A command that goes on to describe the whole compilation has read past the first error
     * already, and showing one beside an account of everything else leaves a reader to wonder what
     * the rest of them were.
     */
    @Test
    void bothProblemsAreSaidRatherThanTheFirstOfThem() throws Exception {
        Streams ran = run(TWO_BEHAVIORS_DO_NOT_CHECK, "--format", "json");

        assertEquals(1, ran.code());
        assertTrue(ran.err().contains("nope") && ran.err().contains("alsoNope"),
                "neither problem is behind the other, so both are said: " + ran.err());
    }

    /**
     * A selector that resolves, on a compilation that did not.
     *
     * <p>Where the two rules meet. A name that names nothing is refused before a report is made of
     * it, and a name that names something is not — so a subject that resolves and then could not be
     * fully measured comes back as the partial report it is, with the error said beside it, rather
     * than as a usage error about a name that was perfectly good.
     */
    @Test
    void aSelectorThatResolvesStillGetsItsReportFromACompilationThatDidNot() throws Exception {
        Streams ran = run(ONE_BEHAVIOR_DOES_NOT_CHECK, "--format", "json",
                "--module", "example.partly", "--behavior", "take");

        assertEquals(1, ran.code(), "the compilation failed, and the selector was not why");
        assertTrue(ran.err().contains("E1321"), ran.err());
        JsonNode report = JSON.readTree(ran.out());
        assertEquals("example.partly", report.get("modules").get(0).get("module").asString());
        assertEquals(1, report.get("modules").get(0).get("behaviors").size(),
                "the selector narrowed it to the one behavior it named: " + ran.out());
    }

    @Test
    void nothingIsReportedWhereNoModuleFormed() throws Exception {
        Streams ran = run("""
                module example.broken

                data Ok = { n: Int
                """, "--format", "json");

        assertEquals(1, ran.code());
        assertTrue(ran.out().isBlank(),
                "a source that declares no module has no subject to assess: " + ran.out());
    }
}
