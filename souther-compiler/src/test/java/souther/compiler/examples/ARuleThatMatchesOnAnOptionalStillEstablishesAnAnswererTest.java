package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.FailurePhase;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import javax.tools.ToolProvider;

import java.io.File;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior whose rule matches on an optional is applied, and what it answers is held to what the
 * behavior states.
 *
 * <p>#1049 as it was met: every row of such a behavior stopped at
 * {@link FailurePhase#ANSWERER_ESTABLISHMENT}, nothing was applied, and {@code checkContract}
 * answered {@link ContractObservation.Unobserved}. What the run said was that the module
 * {@code souther} could not be read on this compile's side, and that the way to fix it was to add
 * {@code souther} to the project's dependencies — a module the compiler ships as its own
 * resources, which no artifact carries and no model can depend on.
 *
 * <p>Held end to end and not only over the agreement, because that is where it was found: the
 * declarations agreeing is what establishing an answerer asks for, and a reader of a contract test
 * meets the answer two stages further on.
 */
class ARuleThatMatchesOnAnOptionalStillEstablishesAnAnswererTest {

    private static final String MODEL = """
            module probe.opt

            data Tag = String
            data Query = { tag: Tag? }
            data Page = { tags: List<Tag> }

            behavior pick : (query: Query) -> Page
                ensures carries(query, value)

            let carries (query: Query, page: Page): Bool =
                match query.tag with
                    | None   -> true
                    | Some t -> List.contains(t, page.tags)

            example pick
                | "a tag" : (Query { tag = Tag("dragons") }) -> Page { tags = [Tag("dragons")] }
            """;

    private static final String ANSWERS = """
            package probe.opt;
            public final class PickImpl extends Pick {
                @Override public Page apply(Query query) {
                    return new Page(java.util.List.of(new Tag("dragons")));
                }
            }
            """;

    /** An answer that carries the tag it was asked for: both oracles admit it. */
    private static final String DROPS_THE_TAG = """
            package probe.opt;
            public final class PickImpl extends Pick {
                @Override public Page apply(Query query) {
                    return new Page(java.util.List.of());
                }
            }
            """;

    @Test
    void aRowOfItIsApplied() throws Exception {
        BoundExamples bound = boundTo(ANSWERS);
        RecordedRow row = bound.rows().getFirst();

        RowEvaluation evaluated = bound.evaluate(row);

        assertEquals(FailurePhase.NONE, evaluated.outcome().failurePhase(),
                () -> "nothing stopped before the implementation was reached: " + evaluated);
        assertTrue(evaluated.held(), row::shown);
    }

    @Test
    void andWhatItAnswersIsHeldToWhatTheBehaviorStates() throws Exception {
        BoundExamples bound = boundTo(ANSWERS);

        assertInstanceOf(ContractObservation.NoClauseWasBroken.class,
                bound.checkContract(bound.rows().getFirst()),
                "the rule was read, and the answer keeps it");
    }

    /** The control: the clause is being asked, and an answer that does not keep it is said as
     *  broken rather than as unobserved. */
    @Test
    void andAnAnswerThatDoesNotKeepItIsSaidAsBroken() throws Exception {
        BoundExamples bound = boundTo(DROPS_THE_TAG);

        assertInstanceOf(ContractObservation.Broken.class,
                bound.checkContract(bound.rows().getFirst()),
                "the answer carries no tag, and the rule says it must");
    }

    // --- harness ---------------------------------------------------------------------------------

    private static BoundExamples boundTo(String implementation) throws Exception {
        Map<String, byte[]> generated =
                Compilation.ofSource(MODEL, "Main").db().ask(new Output.All()).value();
        return SoutherExamples.ofSource(MODEL).bind(builtElsewhere(generated, implementation));
    }

    private static Object builtElsewhere(Map<String, byte[]> generated, String source)
            throws Exception {
        Path classes = Files.createTempDirectory("souther-optional-contract");
        for (Map.Entry<String, byte[]> e : generated.entrySet()) {
            Path at = classes.resolve(e.getKey().replace('.', '/') + ".class");
            Files.createDirectories(at.getParent());
            Files.write(at, e.getValue());
        }
        Path java = classes.resolve("probe/opt/PickImpl.java");
        Files.createDirectories(java.getParent());
        Files.writeString(java, source);
        int rc = ToolProvider.getSystemJavaCompiler().run(null, null, null,
                "-encoding", "UTF-8",
                "-classpath", classes + File.pathSeparator + System.getProperty("java.class.path"),
                "-d", classes.toString(), java.toString());
        assertEquals(0, rc, "the implementation compiles against the module's classes");
        URLClassLoader loader = new URLClassLoader(new URL[] {classes.toUri().toURL()},
                ExampleVerifier.class.getClassLoader());
        return loader.loadClass("probe.opt.PickImpl").getConstructor().newInstance();
    }
}
