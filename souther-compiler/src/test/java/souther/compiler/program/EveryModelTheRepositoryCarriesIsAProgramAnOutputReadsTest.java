package souther.compiler.program;

import souther.compiler.conformance.RepositoryModels;
import souther.compiler.diag.CompileException;
import souther.compiler.query.Compilation;
import souther.test.ClosedWorldContract;
import souther.test.Nightly;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every model this repository carries, whatever it was written for, is a program an output outside
 * the compiler can read.
 *
 * <p>A program the checker takes and {@link CheckedProgram#of} refuses is one every backend reading
 * the program API stops on while the JVM compiles it. The rules {@link CheckedModule} holds itself to
 * are about how its parts agree, and the models are where those parts are written the way somebody
 * writes them — values in an attached file among them — rather than the way a test about one part
 * writes it.
 *
 * <p>Taken from the compilations {@link RepositoryModels} already answered, through the assembler's
 * entry for a compilation in hand, which asks the same verdict and makes the same snapshot as the
 * entry an output calls with sources.
 *
 * <p>Asked once a night. It is a property of every model the repository carries as the corpus runs
 * it, and no smaller set stands for that; what it finds is as well found by the morning as by the
 * change that caused it.
 */
@ClosedWorldContract
@Nightly
class EveryModelTheRepositoryCarriesIsAProgramAnOutputReadsTest {

    /**
     * Of the models the language accepts. A conformance corpus may be written to draw an error, and
     * a program the language refuses is one the program API is right to refuse; the language's
     * verdict is answered as a {@link CompileException}, by {@code Acceptance}, and by nothing else.
     */
    @Test
    void everyModelTheLanguageAcceptsIsReadAsACheckedProgram() {
        List<String> read = new ArrayList<>();
        List<String> refused = new ArrayList<>();
        for (Map.Entry<String, Compilation> corpus : RepositoryModels.byCorpus().entrySet()) {
            try {
                CheckedProgramAssembler.of(corpus.getValue());
                read.add(corpus.getKey());
            } catch (CompileException e) {
                // The language refused it, so there is no program to read.
            } catch (IllegalStateException e) {
                read.add(corpus.getKey());
                refused.add(corpus.getKey() + ": " + e.getMessage());
            }
        }
        assertEquals(List.of(), refused, "models the language accepts and the program API refuses");
        assertTrue(read.contains("crm"),
                () -> "a model writing values in an attached file was not read; read " + read);
    }
}
