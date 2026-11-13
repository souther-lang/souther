package souther.bench;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a corpus is checked with stops for a model that does not compile.
 *
 * <p>{@code ATestThatReadsAModelsReportAsksThatTheModelCompilesTest} takes a model handed to
 * {@link Corpus#check} to be asked about once the call returns, so that a test that goes through it
 * does not also have to go through the helper. That holds only if the call returns for a model that
 * compiles and for no other, which is what is held here.
 */
class ACorpusCheckStopsForAModelThatDoesNotCompileTest {

    @Test
    void aModelWithAnErrorIsNotOneTheCheckReturnsFor() {
        Compilation broken = Compilation.ofSource("""
                module bad

                let x = missing
                """, "Main");

        assertThrows(RuntimeException.class, () -> Corpus.all().getFirst().check(broken),
                "a model that does not compile is one the check goes on from");
    }
}
