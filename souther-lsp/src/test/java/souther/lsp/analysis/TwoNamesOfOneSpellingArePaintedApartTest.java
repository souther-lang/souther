package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.DocumentHighlight;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a highlight is about is a name, not a spelling. Two locals written {@code x} are two names,
 * and painting both because the characters match would tell a reader that editing one reaches the
 * other.
 */
class TwoNamesOfOneSpellingArePaintedApartTest {

    private static final String URI = "file:///m.sou";
    private static final String LIB_URI = "file:///lib.sou";

    /** Two behaviors, each binding an `x` of its own. */
    private static final String SHADOWED = """
            module m

            behavior first : (x: Int) -> Int
            let first (x) = x + x

            behavior second : (x: Int) -> Int
            let second (x) = x
            """;

    @Test
    void onlyTheBindingTheCursorIsInIsPainted() {
        // the `x` read on line 3, inside `first`
        List<DocumentHighlight> painted = highlights(SHADOWED, at(3, 16));

        assertEquals(3, painted.size(),
                "the parameter of `first` and its two reads, and nothing of `second`");
        for (DocumentHighlight each : painted) {
            assertEquals(3, each.range().start().line(),
                    "every one of them is on the line `first` is written on");
        }
    }

    @Test
    void whereTheNameIsBoundIsToldFromWhereItIsRead() {
        List<DocumentHighlight> painted = highlights(SHADOWED, at(3, 16));
        List<Integer> bound = new ArrayList<>();
        for (DocumentHighlight each : painted) {
            if (each.kind() == DocumentHighlight.WRITE) {
                bound.add(each.range().start().character());
            }
        }

        assertEquals(List.of(SHADOWED.lines().toList().get(3).indexOf("(x)") + 1), bound,
                "one of them binds the name, and it is the one in the `let`'s brackets");
    }

    /**
     * And nothing of another file is painted in this one.
     *
     * <p>A name declared elsewhere is referenced in both files, and what a highlight is drawn on is
     * the document being read. What is checked is the keeping-to-one-document, which is the whole of
     * what this adds to the references answer — where those references are is that answer's to say
     * and is checked where it is written.
     */
    @Test
    void nothingOfAnotherFileIsPaintedInThisOne() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(LIB_URI, """
                module lib exposing ( Cost )

                data Cost = { amount: Int }
                """);
        sources.put(URI, """
                module m

                import lib ( Cost )

                behavior priced : (c: Cost) -> Int
                let priced (c) = c.amount
                """);

        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        Position onCost = at(4, 22);

        List<String> filesReferenced = new ArrayList<>();
        for (souther.lsp.protocol.Location each
                : analyzer.references(URI, onCost, graph, true)) {
            filesReferenced.add(each.uri());
        }

        assertTrue(filesReferenced.contains(LIB_URI),
                "`Cost` is referenced in the file that declares it, which is the other one");
        assertTrue(!analyzer.documentHighlights(URI, onCost, graph).isEmpty(),
                "and in this one, which is what is painted");
        assertEquals(List.of(), outsideThisDocument(analyzer, URI, onCost, graph),
                "and nothing of the other file is painted here");
    }

    /** Every highlight this document was given that is not in it — none, by construction, which is
     *  what makes the emptiness worth asserting. */
    private static List<Object> outsideThisDocument(Analyzer analyzer, String uri, Position pos,
                                                    ModuleGraph graph) {
        List<Object> stray = new ArrayList<>();
        List<Range> here = new ArrayList<>();
        for (souther.lsp.protocol.Location each : analyzer.references(uri, pos, graph, true)) {
            if (uri.equals(each.uri())) {
                here.add(each.range());
            }
        }
        for (DocumentHighlight each : analyzer.documentHighlights(uri, pos, graph)) {
            if (!here.contains(each.range())) {
                stray.add(each.range());
            }
        }
        return stray;
    }

    private static Position at(int line, int character) {
        return new Position(line, character);
    }

    private static List<DocumentHighlight> highlights(String text, Position pos) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, text);
        return highlights(sources, URI, pos);
    }

    private static List<DocumentHighlight> highlights(Map<String, String> sources, String uri,
                                                      Position pos) {
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return analyzer.documentHighlights(uri, pos, graph);
    }
}
