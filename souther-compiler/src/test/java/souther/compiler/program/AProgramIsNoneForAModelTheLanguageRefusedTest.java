package souther.compiler.program;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A program is read of a model only where the language accepts it.
 *
 * <p>{@code ATestThatReadsAModelsReportAsksThatTheModelCompilesTest} takes a model handed to
 * {@code CheckedProgramAssembler.of} to be asked about once the call returns, so that a test that
 * goes through it does not also have to go through the helper. That holds only if the call returns
 * for a model that compiles and for no other, which is what is held here.
 */
class AProgramIsNoneForAModelTheLanguageRefusedTest {

    @Test
    void aModelWithAnErrorIsNotOneAProgramIsReadOf() {
        Compilation broken = Compilation.ofSource("""
                module bad

                let x = missing
                """, "Main");

        assertThrows(CompileException.class, () -> CheckedProgramAssembler.of(broken),
                "a model that does not compile is one a program is read of");
    }
}
