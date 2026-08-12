package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Find-references asked the module for every place it names a type and then filed all of them under
 * the module's own file. A module's names are not all written in one file, so a use written in an
 * attached {@code examples for} file was published in the model file at the line and column it has in
 * the other one — a place in a file it is not in, and one that may well hold something else.
 *
 * <p>Where a use is written is what the answer already says; only the reading of it was module-wide.
 */
class AUseIsFoundInTheFileItIsWrittenInTest {

    private static final String MODEL_URI = "file:///m.sou";
    private static final String ATTACHED_URI = "file:///m.examples.sou";

    /** Names `D` on line 3, twice on line 4 and twice on line 8. */
    private static final String MODEL = """
            module m

            data D = { v: Int }
            behavior f : (d: D) -> D
            let f (d) = d

            example f
                | "a" : (D { v = 1 }) -> D { v = 1 }
            """;

    /** Names `D` on line 3 and line 6 — both past the end of what the model file writes. */
    private static final String ATTACHED = """
            examples for m

            let base = D { v = 2 }

            example f
                | "b" : (base) -> D { v = 2 }
            """;

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(MODEL_URI, MODEL);
        sources.put(ATTACHED_URI, ATTACHED);
        return ModuleGraph.of(sources);
    }

    /** Every use of `D`, asked from the one the model file's `behavior` line writes. */
    private static List<Location> usesOfD() {
        ModuleGraph graph = graph();
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return analyzer.references(MODEL_URI, new Position(3, 17), graph, false);
    }

    @Test
    void theUsesTheAttachedFileWritesAreFoundThere() {
        List<Location> found = usesOfD();

        assertEquals(2, found.stream().filter(l -> l.uri().equals(ATTACHED_URI)).count(),
                "the attached file names `D` twice: " + found);
    }

    @Test
    void andAreNotAlsoReportedInTheModelFile() {
        List<Location> found = usesOfD();

        assertEquals(4, found.stream().filter(l -> l.uri().equals(MODEL_URI)).count(),
                "the model file names `D` four times besides declaring it: " + found);
    }

    @Test
    void everyPlaceFoundReallySpellsTheNameThere() {
        Map<String, String> text = new LinkedHashMap<>();
        text.put(MODEL_URI, MODEL);
        text.put(ATTACHED_URI, ATTACHED);

        for (Location found : usesOfD()) {
            List<String> lines = text.get(found.uri()).lines().toList();
            assertTrue(found.range().start().line() < lines.size(),
                    "line " + found.range().start().line() + " is past the end of " + found.uri());
            String line = lines.get(found.range().start().line());
            assertEquals("D", line.substring(found.range().start().character(),
                            found.range().end().character()),
                    "at " + found.uri() + " " + found.range());
        }
    }
}
