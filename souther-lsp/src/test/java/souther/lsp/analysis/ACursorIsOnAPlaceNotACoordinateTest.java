package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value a row names may be declared beside the rows, in the attached {@code examples for} file.
 * Where it is declared is what its declaration's position says; working it out from the module
 * instead is right only while a module is one file, and this is the case where it is not.
 *
 * <p>Before, the cursor was sent to the module's own file at the coordinate the declaration has in
 * the other one — which, here, is the cursor's own line. Go-to-definition landed back where it
 * started.
 */
class ACursorIsOnAPlaceNotACoordinateTest {

    private static final String MODEL_URI = "file:///m.sou";
    private static final String ATTACHED_URI = "file:///m.examples.sou";

    /** The row on line 8 names `もと`, which this file does not declare. */
    private static final String MODEL = """
            module m

            data D = { v: Int }
            behavior f : (d: D) -> D
            let f (d) = d

            example f
                | "a" : (もと) -> D { v = 1 }
            """;

    private static final String ATTACHED = """
            examples for m

            let もと = D { v = 1 }
            """;

    private static Optional<Location> definitionFromTheRow() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(MODEL_URI, MODEL);
        sources.put(ATTACHED_URI, ATTACHED);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        // the `もと` of the row: line 8 column 14 as the compiler counts, zero-based here
        return analyzer.definition(MODEL_URI, new Position(7, 13), graph);
    }

    @Test
    void aValueTheRowNamesIsFoundInTheFileThatDeclaresIt() {
        Location found = definitionFromTheRow().orElseThrow();

        assertEquals(ATTACHED_URI, found.uri(), "the `let` is written beside the rows");
    }

    @Test
    void theCursorLandsOnTheNameAndNotBackWhereItStarted() {
        Location found = definitionFromTheRow().orElseThrow();

        assertEquals(2, found.range().start().line(), "the third line of the attached file");
        String declaration = ATTACHED.lines().toList().get(2);
        assertTrue(declaration.substring(found.range().start().character()).startsWith("もと"),
                "on the name it declares: " + found.range());
    }
}
