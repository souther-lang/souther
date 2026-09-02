package souther.compiler.query;

import souther.compiler.observe.ArmObservation;
import org.junit.jupiter.api.Test;

import souther.compiler.codegen.Backend;
import souther.compiler.codegen.Instrumentation;
import souther.compiler.coverage.CoverageSites;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What happens when the plan is not about the bodies being emitted.
 *
 * <p>The one failure a measurement may not be quiet about. A body emitted an arm short reports the arm
 * that ran as one no row reaches, and that reads as a gap in the model — the author goes looking for a
 * row to write against a branch their rows already take. So the arms are looked up by identity, and a
 * node the plan does not hold stops the generation rather than producing a body with a hole in it.
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

    /** The numbering of {@code module}'s bodies as {@code compilation} checked them. Which compile
     *  they were checked by is what the tests below turn on: two compiles of one source number one
     *  arm alike, and a plan of one compile's bodies is about that compile's trees. */
    private static CoverageSites.Plan checkedPlanOf(Compilation compilation, String module) {
        Bodies.Elaborated checked =
                compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        return checked.plan();
    }

    /**
     * A plan made from one compile, used to emit another's bodies.
     *
     * <p>The two compiles are of the same source, so their bodies are equal in every way a record
     * compares. That is exactly the case a value-keyed map would answer confidently and wrongly, and
     * the reason the map is keyed by identity.
     */
    @Test
    void aPlanFromOtherBodiesStopsTheGenerationRatherThanEmitAHole() {
        Compilation emitting = compiled();
        Compilation elsewhere = compiled();
        String module = emitting.modules().get(0);
        Output.Classes.Inputs in = Output.Classes.inputs(emitting.db(), module);
        CoverageSites.Plan somewhereElse = checkedPlanOf(elsewhere, module);
        assertNotNull(in);
        assertTrue(somewhereElse.sites().size() > 0, "the other compile has arms of its own");

        IllegalStateException stopped = assertThrows(IllegalStateException.class,
                () -> Backend.generate(in.lowered(), in.scope(),
                        in.scope().library().kernelSignatures(), in.typePackages(), in.sigs(),
                        in.imported(), in.injected(), in.callees(), in.requirements(), in.checked(),
                        in.compositions(), in.dischargeClauses(), in.shapes(), in.checks(),
                        in.standingCalls(),
                        Instrumentation.NONE.measuring(somewhereElse)));

        assertTrue(stopped.getMessage().contains("no probe was planned"), stopped.getMessage());
    }

    /**
     * An arm the plan counted that nothing put in the bytecode.
     *
     * <p>The other half of the same guarantee, and the half that was missing. A body walked without
     * counting its arms does not fail where it is walked — it just leaves them out, and every one of
     * them then reads as an arm no row goes through. Catching it means comparing what was planned with
     * what was emitted, which can only be done once, at the end.
     */
    @Test
    void anArmPlannedAndNotEmittedStopsTheGeneration() {
        Compilation emitting = compiled();
        String module = emitting.modules().get(0);
        Output.Classes.Inputs in = Output.Classes.inputs(emitting.db(), module);
        assertNotNull(in);
        CoverageSites.Plan real = checkedPlanOf(emitting, module);
        assertTrue(real.sites().size() > 0);

        // The same plan with one more arm in it than any body will emit.
        CoverageSites.Site extra = real.sites().get(0);
        List<CoverageSites.Site> longer = new java.util.ArrayList<>(real.sites());
        longer.add(new CoverageSites.Site(extra.behavior(), extra.outcome(), extra.at(),
                real.sites().size(), real.sites().size(), extra.obligation()));
        CoverageSites.Plan overcounted =
                new CoverageSites.Plan(longer, real.guards(), real.byNode(), real.byComparison(),
                        real.armsByNode(), real.controlByComparison(), real.mayRepeat(),
                        real.forkByNode(), real.comparisons(), real.identity());

        IllegalStateException stopped = assertThrows(IllegalStateException.class,
                () -> Backend.generate(in.lowered(), in.scope(),
                        in.scope().library().kernelSignatures(), in.typePackages(), in.sigs(),
                        in.imported(), in.injected(), in.callees(), in.requirements(), in.checked(),
                        in.compositions(), in.dischargeClauses(), in.shapes(), in.checks(),
                        in.standingCalls(),
                        Instrumentation.NONE.measuring(overcounted)));

        assertTrue(stopped.getMessage().contains("nothing emitted"), stopped.getMessage());
    }

    /** And the plan made from these bodies emits them, so what the case above rejects is the mismatch
     * and not the arrangement. */
    @Test
    void aPlanFromTheseBodiesEmitsThem() {
        Compilation emitting = compiled();
        String module = emitting.modules().get(0);

        assertNotNull(emitting.db().ask(new Output.Evaluated(module, ArmObservation.RECORD)).value());
    }

    /** The query turns that into an answer with nothing in it. What reads it reports a measurement it
     * could not make, which is not the same as a model with a branch nothing reaches. */
    @Test
    void theQueryAnswersWithNothingRatherThanWithAHole() {
        Compilation emitting = compiled();
        Answer<souther.compiler.generated.EvaluationArtifact> probed =
                emitting.db().ask(new Output.Evaluated("no.such.module", ArmObservation.RECORD));

        assertTrue(!probed.present() || probed.value() == null);
    }
}
