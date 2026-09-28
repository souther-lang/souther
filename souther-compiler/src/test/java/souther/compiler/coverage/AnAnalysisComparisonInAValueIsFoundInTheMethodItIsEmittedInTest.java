package souther.compiler.coverage;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Answer;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison the analysis reads in a value is found where the backend emits it.
 *
 * <p>The tree an analysis reads holds what a value compares where the value is named, and the tree
 * the backend emits holds it in the value's method. What a rule about the behavior is read off the
 * first is answered by looking for that comparison in the second, so a reader that looked in the
 * behavior's own emitted body alone would find nothing where there is a comparison.
 */
class AnAnalysisComparisonInAValueIsFoundInTheMethodItIsEmittedInTest {

    private static final String SOURCE = """
            module m exposing (f)

            let base = List.length([1, 2, 3])

            let enough = base > 2

            behavior f : (n: Int) -> Int
            let f (n) = if enough then n else 0
            """;

    @Test
    void theCoverageOfABehaviorIsReadThroughTheMethodsItCalls() {
        Answer<?> coverage = Compiler.compiled(SOURCE, "m").db().ask(new Adequacy.Coverage("m"));

        assertTrue(coverage.present(),
                "a comparison read in `enough` has a counterpart in the method `enough` is emitted as");
        assertFalse(coverage.hasError(), () -> String.valueOf(coverage));
    }
}
