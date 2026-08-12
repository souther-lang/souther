package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A multi-module compile is fail-fast: it reports the first module that does not compile, in the
 * order the modules were given. So a type error in the first module is what the author sees, even
 * when a later module imports one whose pipeline cannot be resolved.
 *
 * <p>This pins the order against an optimization that would resolve every module's imported
 * signatures up front to avoid resolving them twice: doing that runs the third module's pipeline
 * resolution — reached through the second module's import — before the first module is ever
 * checked, and sends the author to the wrong file.
 */
class CompileModuleErrorOrderTest {

    private static final String FIRST_HAS_A_TYPE_ERROR = """
            module m.first exposing ( N, inc )

            data N = Int

            behavior inc : (n: N) -> N constructs N
            let inc (n) = "not an N"
            """;

    private static final String SECOND_IMPORTS_THE_THIRD = """
            module m.second

            import m.third ( p )

            data Z = Int
            """;

    private static final String THIRD_HAS_AN_UNRESOLVABLE_PIPELINE = """
            module m.third exposing ( p )

            behavior p = nosuchstage >-> alsomissing
            """;

    @Test
    void theFirstModulesErrorIsReportedNotOneReachedThroughALaterModulesImport() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(FIRST_HAS_A_TYPE_ERROR,
                        SECOND_IMPORTS_THE_THIRD, THIRD_HAS_AN_UNRESOLVABLE_PIPELINE)));

        assertTrue(e.getMessage().contains("`inc`"),
                "expected the first module's type error, got: " + e.getMessage());
    }
}
