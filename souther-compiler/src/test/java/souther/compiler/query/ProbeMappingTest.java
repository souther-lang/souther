package souther.compiler.query;

import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.generated.ProbeImage;
import souther.compiler.observe.ArmObservation;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whose numbers a run through an evaluation's classes is recorded in.
 *
 * <p>One numbering, and the artifact carries the emission's own answer for it. The numbers written
 * into the bytecode and the numbers a report reads a run back under have to be the same numbering or
 * an arm that ran is credited to a place nothing ran through — and a plan is made from bodies, so
 * anybody holding those bodies can make an equal one and be trusted on it. What the emitter numbered
 * is what the emitter says it numbered, and that is what arrives here.
 */
class ProbeMappingTest {

    private static final String MODEL = """
            module example.trip

            data Submitted = { cost: Int }
            data Waiting = { cost: Int }

            behavior submit : (cost: Int) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (cost) = {
                guard cost <= 100 else Waiting { cost = cost }
                Submitted { cost = cost }
            }
            """;

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        return compilation;
    }

    @Test
    void aMeasuredEvaluationRecordsARunUnderTheNumberingItsBodiesWereGiven() {
        Compilation emitting = compiled();
        String module = emitting.modules().get(0);

        EvaluationArtifact artifact =
                emitting.db().ask(new Output.Evaluated(module, ArmObservation.RECORD)).value();

        assertNotNull(artifact, "the model under test compiles and evaluates");
        ProbeImage.Instrumented probes =
                assertInstanceOf(ProbeImage.Instrumented.class, artifact.probes(),
                        "a measured evaluation records where a run goes");
        Bodies.Elaborated checked = emitting.db().ask(new Bodies.Checked(module)).value();
        assertEquals(checked.plan().identity(), probes.numbering(),
                "the run is recorded under the numbering of the bodies that were emitted");
    }

    /** And an evaluation nobody asked to measure leaves no account at all, which is not an account of
     *  a run that went nowhere. */
    @Test
    void anUnmeasuredEvaluationRecordsNothing() {
        Compilation emitting = compiled();
        String module = emitting.modules().get(0);

        EvaluationArtifact artifact =
                emitting.db().ask(new Output.Evaluated(module, ArmObservation.OMIT)).value();

        assertNotNull(artifact, "the model under test compiles and evaluates");
        assertInstanceOf(ProbeImage.Uninstrumented.class, artifact.probes());
    }

    /** A module this compile has no bodies for has no artifact, which is the query's own answer and
     *  not anything the generation said. */
    @Test
    void aModuleWithNoBodiesHasNoArtifact() {
        Compilation emitting = compiled();

        Answer<EvaluationArtifact> probed =
                emitting.db().ask(new Output.Evaluated("no.such.module", ArmObservation.RECORD));

        assertTrue(!probed.present() || probed.value() == null);
    }
}
