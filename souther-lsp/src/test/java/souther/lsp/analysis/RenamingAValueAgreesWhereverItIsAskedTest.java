package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What renaming edits does not depend on where the cursor was when it was asked.
 *
 * <p>A behavior is declared twice — the {@code behavior} line says what it is, the {@code let} line
 * says what it does — and both write its name. A value's binding is one place, and a use of it is
 * another; asking from either is asking about the same binding.
 *
 * <p>Both directions used to go through matching the spelling, which is blind to which binding a
 * name belongs to but does at least see every line the name is written on. Answering from
 * resolution has to keep that: an answer that rewrites one of a behavior's two declaration lines
 * leaves the module naming something that is no longer there.
 */
class RenamingAValueAgreesWhereverItIsAskedTest {

    private static final String URI = "file:///a.sou";

    /**
     * `g` is declared on line 3 at column 10 and on line 4 at column 5, and used on line 7 at
     * column 13. `x` is bound on line 8 at column 9 and used on line 9 at column 5.
     */
    private static final String SOURCE = """
            module a exposing ( N, g )

            behavior g : (n: N) -> N
            let g (n) = n

            behavior h : (n: N) -> N
            let h (n) = g({
                let x = n
                x
            })

            data N = { v: Int }
            """;

    private static Map<String, List<Range>> renameFrom(Position pos) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, SOURCE);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return analyzer.renameEdits(URI, pos, graph);
    }

    /** The lines an edit set touches, as `line:character`, sorted. */
    private static Set<String> places(Map<String, List<Range>> edits) {
        Set<String> out = new TreeSet<>();
        edits.forEach((uri, ranges) -> ranges.forEach(r ->
                out.add(r.start().line() + ":" + r.start().character())));
        return out;
    }

    @Test
    void renamingABehaviorFromItsSignatureRewritesBothOfItsDeclarations() {
        Set<String> found = places(renameFrom(new Position(2, 9)));

        assertEquals(Set.of("0:23", "2:9", "3:4", "6:12"), found,
                "the `exposing` entry, both declaration lines and the one use");
    }

    @Test
    void renamingABehaviorFromItsBodyRewritesTheSameLines() {
        Set<String> found = places(renameFrom(new Position(3, 4)));

        assertEquals(Set.of("0:23", "2:9", "3:4", "6:12"), found);
    }

    @Test
    void renamingABehaviorFromAUseRewritesTheSameLines() {
        Set<String> found = places(renameFrom(new Position(6, 12)));

        assertEquals(Set.of("0:23", "2:9", "3:4", "6:12"), found,
                "a use is a use of both declarations, not of the signature alone");
    }

    @Test
    void renamingALocalFromItsUseRewritesTheBindingToo() {
        Set<String> found = places(renameFrom(new Position(8, 4)));

        assertEquals(Set.of("7:8", "8:4"), found, "the `let x` and the `x` that reads it");
    }

    @Test
    void renamingALocalFromItsBindingRewritesTheSameLines() {
        Set<String> found = places(renameFrom(new Position(7, 8)));

        assertEquals(Set.of("7:8", "8:4"), found,
                "a binding is what its uses denote, whichever end the question comes from");
    }
}
