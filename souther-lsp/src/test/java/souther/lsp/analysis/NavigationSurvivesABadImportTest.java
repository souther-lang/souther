package souther.lsp.analysis;

import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An import that names nothing does not take the rest of the file with it.
 *
 * <p>A half-typed import line is as ordinary as a half-typed name. What the other imports brought in
 * is still what it is, so the names that resolved still resolve, and only what the bad line was
 * supposed to bring is nameless.
 */
class NavigationSurvivesABadImportTest {

    private static final String UP = """
            module up exposing ( Amount )

            data Amount = Int
            """;

    /**
     * Declares an Amount of its own, names up's qualified, and has an import line that names nothing.
     * The first two are what make matching the spelling give the wrong answer, so an answer that is
     * right here is an answer from what the names denote.
     */
    private static final String HERE = """
            module here exposing ( Amount, Box )

            import m.nope ( Missing )

            data Amount = String

            data Box = { far: up.Amount, near: Amount, bad: Missing }
            """;

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///up.sou", UP);
        sources.put("file:///here.sou", HERE);
        return ModuleGraph.of(sources);
    }

    @Test
    void theImportThatNamesNothingIsReported() {
        assertTrue(new Analyzer().diagnostics(graph()).get("file:///here.sou").stream()
                        .anyMatch(d -> d.message().contains("m.nope")),
                "the import line is what the author is told about");
    }

    @Test
    void aQualifiedReferenceStillGoesToTheModuleItNames() {
        // `far: up.Amount` — up's, not this module's own Amount of the same spelling.
        Optional<Location> found =
                new Analyzer().definition("file:///here.sou", new Position(6, 22), graph());

        assertTrue(found.isPresent(), "up.Amount denotes up's declaration");
        assertEquals("file:///up.sou", found.get().uri(),
                "a spelling match would have stopped at this module's own Amount");
    }

    @Test
    void renamingIsStillAboutWhatNamesDenote() {
        Map<String, java.util.List<souther.lsp.protocol.Range>> edits =
                new Analyzer().renameEdits("file:///here.sou", new Position(4, 5), graph());

        assertTrue(edits.getOrDefault("file:///up.sou", java.util.List.of()).isEmpty(),
                "up declares an Amount of its own, which this rename is not about");
        assertEquals(3, edits.getOrDefault("file:///here.sou", java.util.List.of()).size(),
                "the declaration, the `exposing` entry and the one bare use — not the tail of"
                        + " `up.Amount`, broken import line or not");
    }
}
