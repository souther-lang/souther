package souther.lsp.analysis;

import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Navigation keeps answering about a file that has a mistake somewhere else in it.
 *
 * <p>Half-finished is the normal state of a file in an editor. A compiler that answers only about
 * files with nothing wrong in them answers exactly when the author does not need it — and falling
 * back to matching the spelling is worse than not answering, because it silently does the wrong
 * thing: renaming a type rewrites the tail of a qualified reference to another module's type.
 */
class NavigationSurvivesAMistakeTest {

    private static final String UP = """
            module up exposing ( Amount )

            data Amount = Int
            """;

    /** Names up's Amount, declares one of its own — and names a type that does not exist. */
    private static final String HERE = """
            module here exposing ( Amount, Box )

            data Amount = String

            data Box = { far: up.Amount, near: Amount, oops: Nowhere }
            """;

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///up.sou", UP);
        sources.put("file:///here.sou", HERE);
        return ModuleGraph.of(sources);
    }

    /** Where `data Amount = String` names itself, in here.sou. */
    private static final Position HERES_AMOUNT = new Position(2, 5);

    @Test
    void theMistakeItselfIsReported() {
        assertTrue(new Analyzer().diagnostics(graph()).get("file:///here.sou").stream()
                        .anyMatch(d -> d.message().contains("Nowhere")),
                "the name that denotes nothing is what the author is told about");
    }

    @Test
    void renamingIsStillAboutWhatNamesDenote() {
        Map<String, List<Range>> edits =
                new Analyzer().renameEdits("file:///here.sou", HERES_AMOUNT, graph());

        assertTrue(edits.getOrDefault("file:///up.sou", List.of()).isEmpty(),
                "up declares an Amount of its own, which this rename is not about");
        assertEquals(3, edits.getOrDefault("file:///here.sou", List.of()).size(),
                "the declaration, the `exposing` entry and the one bare use — not the tail of"
                        + " `up.Amount`, mistake in the file or not");
    }
}
