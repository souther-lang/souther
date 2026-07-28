package souther.lsp.analysis;

import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Navigation answers what a name denotes, not what it is spelled.
 *
 * <p>Two modules may declare the same name, and a qualified reference reaches one of them without an
 * import line. Matching the spelling cannot tell those apart: renaming one module's {@code Amount}
 * would rewrite the tail of every {@code other.Amount} written anywhere, which changes what those
 * references mean and stops the workspace compiling.
 */
class NavigationResolvesNamesTest {

    private static final String UP = """
            module up exposing ( Amount )

            data Amount = Int
            """;

    /** Declares an Amount of its own and also names up's, qualified — no import line needed. */
    private static final String HERE = """
            module here exposing ( Amount, Box )

            data Amount = String

            data Box = { far: up.Amount, near: Amount }
            """;

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///up.sou", UP);
        sources.put("file:///here.sou", HERE);
        return ModuleGraph.of(sources);
    }

    /** Where `data Amount = String` names itself, in here.sou. */
    private static final Position HERES_AMOUNT = new Position(2, 5);
    /** Where `up.Amount` names up's, in here.sou. */
    private static final Position THE_QUALIFIED_USE = new Position(4, 22);

    @Test
    void renamingOneModulesTypeLeavesTheOtherModulesAlone() {
        Map<String, List<Range>> edits =
                new Analyzer().renameEdits("file:///here.sou", HERES_AMOUNT, graph());

        assertTrue(edits.getOrDefault("file:///up.sou", List.of()).isEmpty(),
                "up declares an Amount of its own, which this rename is not about");
        List<Range> here = edits.getOrDefault("file:///here.sou", List.of());
        assertEquals(3, here.size(),
                "the declaration, the `exposing` entry, and the one bare use — not the tail of"
                        + " `up.Amount`");
        for (Range r : here) {
            assertTrue(r.start().line() != 4 || r.start().character() != 22,
                    "the qualified reference names up's Amount and must be left alone");
        }
    }

    @Test
    void aQualifiedReferenceGoesToTheModuleItNames() {
        Optional<Location> found =
                new Analyzer().definition("file:///here.sou", THE_QUALIFIED_USE, graph());

        assertTrue(found.isPresent(), "up.Amount denotes up's declaration");
        assertEquals("file:///up.sou", found.get().uri(),
                "a spelling match would have stopped at this module's own Amount");
    }
}
