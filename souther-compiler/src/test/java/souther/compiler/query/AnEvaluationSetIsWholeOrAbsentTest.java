package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.generated.EvaluationArtifact;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The classes an evaluation runs against are all of them or none of them.
 *
 * <p>A set with a hole in it is the worst of the three possible answers. Running against it produces
 * a class that will not load, or one found further up the loader chain that this compile did not
 * generate, or an example that fails for neither reason — and all three read as a fault in the model.
 * The caller has a way to say a measurement could not be made; it has no way to notice a class that
 * quietly was not there.
 */
class AnEvaluationSetIsWholeOrAbsentTest {

    /** Two modules, the imported one written so that it does not check. */
    private static final List<String> ONE_REACHES_A_BROKEN_ONE = List.of("""
            module example.reaches
            import example.broken ( Amount )

            data Out = Int

            behavior run : (a: Amount) -> Out constructs Out

            let run (a) = Out(0)
            """, """
            module example.broken

            data Amount = Int
                invariant value >= "not a number"
            """);

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSources(ONE_REACHES_A_BROKEN_ONE,
                souther.compiler.meta.ModulePath.EMPTY);
        compilation.answerEverything();
        return compilation;
    }

    /** The module that cannot be generated has no evaluation classes. */
    @Test
    void aModuleThatDoesNotCheckHasNoEvaluationClasses() {
        Answer<EvaluationArtifact> broken = compiled().db()
                .ask(new Output.Evaluated("example.broken", Output.CoverageMode.NONE));

        assertNull(broken.value(), "nothing was generated for it");
    }

    /**
     * And the set that reaches it is absent rather than partial.
     *
     * <p>Before, a module that could not be generated was skipped and the rest handed over as a map
     * — always non-null, so the branch downstream that exists to say "these classes could not be
     * made" was never reached.
     */
    @Test
    void aSetThatReachesItIsAbsentRatherThanShortAClass() {
        Answer<EvaluationArtifact> linked = compiled().db()
                .ask(new Output.EvaluationLinked("example.reaches", Output.CoverageMode.NONE));

        assertNull(linked.value(),
                "a set missing the classes of a module the rows can reach is not a set to run");
    }

    /** A module that reaches nothing broken still gets its classes, so the rule above is not simply
     *  refusing everything. */
    @Test
    void aWholeSetIsStillAnswered() {
        Compilation compilation = Compilation.ofSource("""
                module example.whole
                data N = Int
                data Out = Int
                behavior run : (n: N) -> Out constructs Out
                let run (n) = Out(n.value)
                """, "Main");
        compilation.answerEverything();

        EvaluationArtifact linked = compilation.db()
                .ask(new Output.EvaluationLinked("example.whole", Output.CoverageMode.NONE)).value();

        assertNotNull(linked);
        assertFalse(linked.classes().isEmpty(), "the module's own classes are there");
    }
}
