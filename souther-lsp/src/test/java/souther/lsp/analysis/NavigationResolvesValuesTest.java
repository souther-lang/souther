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
}
