package souther.compiler.program;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.diag.CompileException;
import souther.test.ClosedWorldContract;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

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
 */
@ClosedWorldContract
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
        for (String corpus : ConformanceCorpus.manifest().keySet()) {
            try {
                CheckedProgram.of(ConformanceCorpus.sourcesOf(corpus));
                read.add(corpus);
            } catch (CompileException e) {
                // The language refused it, so there is no program to read.
            } catch (IllegalStateException e) {
                read.add(corpus);
                refused.add(corpus + ": " + e.getMessage());
            }
        }
        assertEquals(List.of(), refused, "models the language accepts and the program API refuses");
        assertTrue(read.contains("crm"),
                () -> "a model writing values in an attached file was not read; read " + read);
    }
}
