package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ArmObservation;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fork whose arms answer functions is a fork, and both halves of the count know it.
 *
 * <p>What an arm answers with does not decide whether a row took it. A choice between two rules is
 * written as a condition like any other, a row goes down one side of it, and the side it went down
 * is what a measure of that behavior is about — so the numbering holds an arm for it and the
 * bytecode has to carry the arm's probe.
 *
 * <p>Held as a pair on purpose. The numbering is made from the checked bodies and the probes are
 * written by the emitter, and either of them alone is satisfied by a fork nobody counts: a plan with
 * an arm nothing emits reports the arm as one no row reaches, which reads as a gap in the model
 * rather than as a hole in the measurement.
 */
class AForkThatAnswersAFunctionIsCountedLikeAnyOtherTest {

    private static final String MODULE = "example.chosen";

    private static final String MODEL = """
            module example.chosen

            data Count = Int

            behavior tally : (positive: Bool, xs: List<Int>) -> Count
                constructs Count
            let tally (positive, xs) = {
                let p: (Int) -> Bool =
                    if positive then (x) -> x > 0 else (x) -> x < 0

                Count(List.length(List.filter(p, xs)))
            }
            """;

    private final Compilation compilation =
            Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);

    private Bodies.Elaborated checked() {
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(MODULE)).value();
        assertNotNull(checked, "the model under test compiles");
        return checked;
    }

    @Test
    void theNumberingHoldsAnArmForTheForkThatChoosesTheRule() {
        CoverageSites.Plan plan = checked().plan();

        assertTrue(plan.byNode().keySet().stream()
                        .anyMatch(node -> node instanceof Core.If it
                                && it.then().type() instanceof Type.FnOf),
                () -> "no fork answering a function was numbered, so the case below would hold of a"
                        + " model this test is not about: " + plan.byNode().keySet());
    }

    /** And the emission carries every one of them, which is what the generation says by finishing:
     *  an arm the plan numbered and nothing wrote stops it. */
    @Test
    void theEmissionCarriesEveryArmThePlanNumbered() {
        EvaluationArtifact artifact = compilation.db()
                .ask(new Output.Evaluated(MODULE, ArmObservation.RECORD)).value();

        assertNotNull(artifact, "the module was generated with its arms recorded");
    }
}
