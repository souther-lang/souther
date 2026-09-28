package souther.program.api;

import souther.compiler.Compiler;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.program.BehaviorTarget;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedImplementation;
import souther.compiler.program.CheckedProgram;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What constructing a behavior requires injected is answered by the program for every behavior a
 * call reaches — one a module read off the path declares as much as one of this compile.
 *
 * <p>A composition here hands each stage the dependencies that stage's constructor takes, picked
 * from its own. So an output building one has to know what a stage requires whichever module
 * declares it, and for a stage the declaring build emitted, what that build published is the only
 * place the answer is.
 */
class AStageOffThePathSaysWhatConstructingItRequiresTest {

    /**
     * Two behaviors left to Java, a stage that depends on them in an order that is not their
     * alphabetical one, and a behavior nobody has written that depends on one of them.
     */
    private static final String PUBLISHED = """
            module lib.stage exposing ( priceOf, feeOf, stage, owed )
            behavior priceOf : (n: Int) -> Int
            behavior feeOf : (n: Int) -> Int

            behavior stage : (n: Int) -> Int
                depends on priceOf, feeOf
            let stage (n, priceOf, feeOf) = priceOf(n) + feeOf(n)

            behavior owed : (n: Int) -> Int
                depends on feeOf
            """;

    /** Names neither dependency: what it requires comes in through the stage. */
    private static final String USES = """
            module app.run
            import lib.stage ( stage )

            behavior finish : (n: Int) -> Int
            let finish (n) = n + 1

            behavior run = stage >-> finish
            """;

    private static final ValueName.Behavior PRICE_OF = new ValueName.Behavior("lib.stage",
            "priceOf");
    private static final ValueName.Behavior FEE_OF = new ValueName.Behavior("lib.stage", "feeOf");
    private static final ValueName.Behavior STAGE = new ValueName.Behavior("lib.stage", "stage");
    private static final ValueName.Behavior OWED = new ValueName.Behavior("lib.stage", "owed");
    private static final ValueName.Behavior RUN = new ValueName.Behavior("app.run", "run");
    private static final ValueName.Behavior FINISH = new ValueName.Behavior("app.run", "finish");

    @Test
    void aStageAnotherBuildEmittedSaysWhatItsConstructorTakesInOrder() {
        BehaviorTarget stage = offThePath().behavior(STAGE);

        assertInstanceOf(CheckedImplementation.ImplementedElsewhere.class, stage.implementation());
        assertEquals(List.of(PRICE_OF, FEE_OF), stage.requirements(),
                "in the order the declaring module's constructor takes them, which is the order"
                        + " its depends on names them and not the order their names sort in");
    }

    /** And it is the same answer as when the declaring module is compiled here: which way a module
     *  arrived is not something what its behaviors require depends on. */
    @Test
    void itIsWhatTheDeclaringModuleAnswersWhenCompiledHere() {
        CheckedProgram together = CheckedProgram.of(List.of(PUBLISHED, USES));

        assertEquals(together.behavior(STAGE).requirements(),
                offThePath().behavior(STAGE).requirements());
    }

    /** The composition here requires what its stage does, and the two lists are the one a stage's
     *  context is picked from and the one it is picked into. */
    @Test
    void aCompositionHereRequiresWhatItsStageOffThePathRequires() {
        CheckedProgram program = offThePath();

        assertEquals(program.behavior(STAGE).requirements(), program.behavior(RUN).requirements());
    }

    /** An injected behavior on the path requires nothing to construct: Souther does not construct
     *  it, and it is itself what the stage depends on. */
    @Test
    void anInjectedBehaviorOnThePathRequiresNothingToConstruct() {
        BehaviorTarget priceOf = offThePath().behavior(PRICE_OF);

        assertInstanceOf(CheckedImplementation.Injected.class, priceOf.implementation());
        assertEquals(List.of(), priceOf.requirements());
    }

    /** A behavior nobody has written requires what it declares it depends on: where its
     *  implementation comes from is a separate question from what constructing it takes. */
    @Test
    void anUnwrittenBehaviorOnThePathRequiresWhatItDependsOn() {
        BehaviorTarget owed = offThePath().behavior(OWED);

        assertInstanceOf(CheckedImplementation.Unwritten.class, owed.implementation());
        assertEquals(List.of(FEE_OF), owed.requirements());
    }

    /** A behavior of a checked module says what it requires once: reached through its module or
     *  through its identity, it is the same list. */
    @Test
    void aCheckedBehaviorsRequirementsAreItsTargetsRequirements() {
        CheckedProgram program = offThePath();

        CheckedBehavior run = program.module("app.run").behavior(RUN);
        CheckedBehavior finish = program.module("app.run").behavior(FINISH);

        assertSame(program.behavior(RUN).requirements(), run.requirements());
        assertSame(program.behavior(FINISH).requirements(), finish.requirements());
        assertEquals(List.of(), finish.requirements());
    }

    private static CheckedProgram offThePath() {
        Map<String, ClassFileImage> published = Compiler.compile(PUBLISHED);
        return CheckedProgram.of(List.of(USES), ModulePath.of(published));
    }
}
