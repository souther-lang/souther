package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An attached {@code examples for} file declares no module of its own, and the editor used to work
 * out which module a document was about by reading its header. So a cursor inside one reached no
 * compile at all: the names it is on are the module's names, and nothing asked the module about
 * them.
 *
 * <p>What the attached file writes is out of reach of a spelling match from either side. It declares
 * no {@code data} and writes no imports, so a type it names is found nowhere; and a local it binds is
 * under a top-level name, which a scan of top-level declarations does not see.
 */
class NavigationInsideAnAttachedFileTest {

    private static final String MODEL_URI = "file:///m.sou";
    private static final String ATTACHED_URI = "file:///m.examples.sou";

    /** `D` is declared on line 3, at column 6. */
    private static final String MODEL = """
            module m

            data D = { v: Int }
            behavior f : (d: D) -> D
            let f (d) = d

            example f
                | "a" : (D { v = 1 }) -> D { v = 1 }
            """;

    /**
     * Line 3 declares `base` at column 5, line 4 binds the local `one` at column 9, line 5 names `D`
     * at column 5 and reads `one` at column 13, and the row on line 9 reads `base` at column 14 and
     * names `D` at column 23.
     */
    private static final String ATTACHED = """
            examples for m

            let base = {
                let one = 2
                D { v = one }
            }

            example f
                | "b" : (base) -> D { v = 2 }
            """;

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(MODEL_URI, MODEL);
        sources.put(ATTACHED_URI, ATTACHED);
        return ModuleGraph.of(sources);
    }

    private static Analyzer warmed(ModuleGraph graph) {
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return analyzer;
    }

    /** The line of {@code text} the location points into, with its range marked by {@code [ ]}. */
    private static String marked(String text, Range range) {
        String line = text.lines().toList().get(range.start().line());
        return line.substring(0, range.start().character()) + "["
                + line.substring(range.start().character(), range.end().character()) + "]"
                + line.substring(range.end().character());
    }

    @Test
    void bothFilesAreCleanSoNothingBelowIsAboutAFileThatDoesNotCompile() {
        Map<String, List<souther.lsp.protocol.LspDiagnostic>> found = new Analyzer()
                .diagnostics(graph());

        assertEquals(List.of(), found.get(MODEL_URI));
        assertEquals(List.of(), found.get(ATTACHED_URI));
    }

    @Test
    void aTypeTheAttachedFileNamesGoesToTheModuleThatDeclaresIt() {
        ModuleGraph graph = graph();

        Location found = warmed(graph)
                .definition(ATTACHED_URI, new Position(4, 4), graph).orElseThrow();

        assertEquals(MODEL_URI, found.uri(), "`D` is declared in the module's own file");
        assertEquals("data [D] = { v: Int }", marked(MODEL, found.range()));
    }

    @Test
    void aTypeNamedByARowInTheAttachedFileGoesThereToo() {
        ModuleGraph graph = graph();

        Location found = warmed(graph)
                .definition(ATTACHED_URI, new Position(8, 22), graph).orElseThrow();

        assertEquals(MODEL_URI, found.uri());
        assertEquals("data [D] = { v: Int }", marked(MODEL, found.range()));
    }

    @Test
    void aValueTheAttachedFileDeclaresIsFoundBesideTheRowThatReadsIt() {
        ModuleGraph graph = graph();

        Location found = warmed(graph)
                .definition(ATTACHED_URI, new Position(8, 13), graph).orElseThrow();

        assertEquals(ATTACHED_URI, found.uri());
        assertEquals("let [base] = {", marked(ATTACHED, found.range()));
    }

    @Test
    void aLocalBoundInTheAttachedFileIsTheBindingAndNotSomeTopLevelName() {
        ModuleGraph graph = graph();

        Location found = warmed(graph)
                .definition(ATTACHED_URI, new Position(4, 12), graph).orElseThrow();

        assertEquals(ATTACHED_URI, found.uri());
        assertEquals("    let [one] = 2", marked(ATTACHED, found.range()));
    }

    @Test
    void findingReferencesFromTheAttachedFileFindsBothFiles() {
        ModuleGraph graph = graph();

        List<Location> found =
                warmed(graph).references(ATTACHED_URI, new Position(4, 4), graph, false);

        assertTrue(found.stream().anyMatch(l -> l.uri().equals(MODEL_URI)),
                "the module's own file names `D` four times: " + found);
        assertTrue(found.stream().anyMatch(l -> l.uri().equals(ATTACHED_URI)),
                "and the attached file twice: " + found);
    }

    @Test
    void renamingFromTheAttachedFileReachesTheDeclaringFile() {
        ModuleGraph graph = graph();

        Map<String, List<Range>> edits =
                warmed(graph).renameEdits(ATTACHED_URI, new Position(4, 4), graph);

        assertTrue(edits.containsKey(MODEL_URI),
                "renaming `D` from here rewrites where it is declared: " + edits);
        assertTrue(edits.containsKey(ATTACHED_URI),
                "and where this file names it: " + edits);
    }
}
