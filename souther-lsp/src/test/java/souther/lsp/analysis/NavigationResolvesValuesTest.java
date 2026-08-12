package souther.lsp.analysis;

import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;
import souther.lsp.protocol.TextEdit;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Navigation on a name used as a value answers what it denotes.
 *
 * <p>A spelling cannot say which binding a use belongs to — one spelling may be bound in several
 * bodies, and a body may bind a name the module also declares — so a local was out of reach and a
 * helper was found by matching text. Resolution answers both, and navigation reads the answer.
 */
class NavigationResolvesValuesTest {

    private static final String SOURCE = """
            module demo exposing ( f )

            let double (n: Int): Int = n * 2

            behavior f : (double: Int) -> Int
            let f (double) = double + 1

            behavior g : (n: Int) -> Int
            let g (n) = double(n)
            """;

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///demo.sou", SOURCE);
        return ModuleGraph.of(sources);
    }

    /** The `double` of `double + 1`, which is f's parameter. */
    private static final Position THE_PARAMETER_USE = new Position(5, 17);
    /** The `double` of `double(n)`, which is the module's helper. */
    private static final Position THE_HELPER_CALL = new Position(8, 12);

    @Test
    void aUseOfAParameterGoesToTheParameter() {
        Optional<Location> found = new Analyzer()
                .definition("file:///demo.sou", THE_PARAMETER_USE, graph());

        assertTrue(found.isPresent(), "a binding is where its name was bound");
        assertEquals(5, found.get().range().start().line(),
                "f's parameter, on f's own line: " + found.get());
    }

    /** The same spelling, one line apart, naming the module's helper rather than the parameter. */
    @Test
    void aCallOfTheHelperGoesToTheHelper() {
        Optional<Location> found = new Analyzer()
                .definition("file:///demo.sou", THE_HELPER_CALL, graph());

        assertTrue(found.isPresent(), "the helper is declared in this file");
        assertEquals(2, found.get().range().start().line(),
                "the `let double` declaration: " + found.get());
    }

    private static final String UP = """
            module up exposing ( Amount )

            data Amount = Int
            """;

    /** Declares an Amount of its own, and builds up's through an alias. */
    private static final String HERE = """
            module here exposing ( Amount, f )

            import up as B

            data Amount = String

            behavior f : (n: Int) -> B.Amount
                constructs B.Amount
            let f (n) = B.Amount(n)
            """;

    private static ModuleGraph twoModules() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///up.sou", UP);
        sources.put("file:///here.sou", HERE);
        return ModuleGraph.of(sources);
    }

    /** The `Amount` of `B.Amount(n)`, in here.sou. */
    private static final Position THE_QUALIFIED_CONSTRUCTION = new Position(8, 16);

    /**
     * A newtype applied to the value it wraps names a type, and the name is answered like any other
     * mention of it. Matching the spelling sent this to whatever the file declared by that name —
     * here, a different type in this very module.
     */
    @Test
    void aQualifiedConstructionGoesToTheTypeItNames() {
        Optional<Location> found = new Analyzer()
                .definition("file:///here.sou", THE_QUALIFIED_CONSTRUCTION, twoModules());

        assertTrue(found.isPresent(), found.toString());
        assertEquals("file:///up.sou", found.get().uri(),
                "`B.Amount` names up's Amount, not the one this module declares: " + found.get());
    }

    /**
     * And renaming that type rewrites the construction with everything else. Leaving it behind is a
     * rename that stops the workspace compiling, which is worse than one that does nothing.
     */
    @Test
    void renamingATypeRewritesTheConstructionsOfItInBodies() {
        Map<String, List<TextEdit>> edits = new Analyzer()
                .renameEdits("file:///up.sou", new Position(2, 5), twoModules(), "Renamed");

        List<Range> here = ranges(edits.get("file:///here.sou"));
        assertTrue(here.stream().anyMatch(r -> r.start().line() == 8 && r.start().character() == 14),
                "the `Amount` of `B.Amount(n)` on the last line: " + here);
        assertEquals(3, here.size(),
                "the output, the `constructs`, and the construction — not this module's own Amount: "
                        + here);
    }

    /** The places a set of edits touches; these tests are about where a rename reaches. What each
     * edit writes is {@code RenamedSourceStillCompilesTest}'s. */
    private static List<Range> ranges(List<TextEdit> edits) {
        return edits == null ? List.of() : edits.stream().map(TextEdit::range).toList();
    }
}
