package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;
import souther.lsp.protocol.TextEdit;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rename is right when the source it produces means what the source it replaced meant. Checking
 * the places an edit set touches does not say that: it says the editor found the occurrences it was
 * looking for, which is a claim about the search and not about the result.
 *
 * <p>The difference is a form where one token has two jobs. A record pattern's {@code { right }}
 * both names the field to read and binds the value to a name of the same spelling. Renaming the
 * binding to {@code r} by writing {@code r} over that token gives {@code { r }}, which reads a field
 * called {@code r} — and there is none. The edit set was right about where; only what to write there
 * was wrong, and a check that reads positions cannot see it.
 */
class RenamedSourceStillCompilesTest {

    private static final String URI = "file:///a.sou";

    /**
     * Line 9 destructures a parameter, naming one field and taking the other's own name. Line 14
     * does the same in a {@code match} arm, and line 19 opens a newtype.
     */
    private static final String SOURCE = """
            module a exposing ( Pair, Round, Flat, Shape, Amount, pick, tag, held )

            data Pair = { left: Int, right: Int }
            data Round = { r: Int }
            data Flat = { f: Int }
            data Shape = Round | Flat

            behavior pick : (p: Pair) -> Int
            let pick ({ left = l, right }) = l + right

            behavior tag : (s: Shape) -> Int
            let tag (s) = match s with
                | Round as w -> w.r
                | Flat { f } -> f

            data Amount = Int

            behavior held : (a: Amount) -> Int
            let held (Amount(inner)) = inner
            """;

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, SOURCE);
        return ModuleGraph.of(sources);
    }

    /** The source as it stands after the rename an editor would carry out. */
    private static String renamed(Position at, String newName) {
        ModuleGraph graph = graph();
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        List<TextEdit> edits = analyzer.renameEdits(URI, at, graph, newName).get(URI);
        assertFalse(edits == null || edits.isEmpty(), "nothing to rename at " + at);
        return applied(SOURCE, edits);
    }

    /** {@code edits} written into {@code text}, back to front so earlier ranges keep their places. */
    private static String applied(String text, List<TextEdit> edits) {
        List<String> lines = new ArrayList<>(text.lines().toList());
        List<TextEdit> ordered = new ArrayList<>(edits);
        ordered.sort(Comparator
                .comparingInt((TextEdit e) -> e.range().start().line())
                .thenComparingInt(e -> e.range().start().character())
                .reversed());
        for (TextEdit edit : ordered) {
            Range r = edit.range();
            assertEquals(r.start().line(), r.end().line(), "an edit spanning lines: " + r);
            String line = lines.get(r.start().line());
            lines.set(r.start().line(), line.substring(0, r.start().character())
                    + edit.newText() + line.substring(r.end().character()));
        }
        return String.join("\n", lines) + "\n";
    }

    /** Whether a source compiles on its own with nothing said about it. */
    private static List<String> problemsIn(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(URI, source);
        List<String> out = new ArrayList<>();
        Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY).diagnostics()
                .forEach((id, found) -> found.forEach(d -> out.add(d.toString())));
        return out;
    }

    @Test
    void theSourceItStartsFromCompiles() {
        assertEquals(List.of(), problemsIn(SOURCE));
    }

    @Test
    void renamingANameWrittenBesideItsFieldLeavesTheFieldAlone() {
        String after = renamed(new Position(8, 19), "amount");   // the `l` of `{ left = l }`

        assertTrue(after.contains("{ left = amount, right }"), after);
        assertEquals(List.of(), problemsIn(after));
    }

    @Test
    void renamingANameTakenFromItsFieldWritesTheFieldBackIn() {
        String after = renamed(new Position(8, 22), "howMany");   // the `right` of `{ right }`

        assertTrue(after.contains("{ left = l, right = howMany }"),
                "`{ right }` binds by taking the field's own name; a rename has to say which"
                        + " field it is reading now that the two differ:\n" + after);
        assertEquals(List.of(), problemsIn(after));
    }

    @Test
    void andTheSameInAMatchArm() {
        String after = renamed(new Position(13, 13), "value");   // the `f` of `| Flat { f }`

        assertTrue(after.contains("| Flat { f = value } -> value"), after);
        assertEquals(List.of(), problemsIn(after));
    }

    @Test
    void aNameANewtypePatternOpensIsRenamedAsItIs() {
        String after = renamed(new Position(18, 17), "amount");   // the `inner` of `Amount(inner)`

        assertTrue(after.contains("let held (Amount(amount)) = amount"), after);
        assertEquals(List.of(), problemsIn(after));
    }

    @Test
    void andSoIsAnOrdinaryParameter() {
        String after = renamed(new Position(11, 9), "shape");   // the `s` of `let tag (s)`

        assertTrue(after.contains("let tag (shape) = match shape with"), after);
        assertEquals(List.of(), problemsIn(after));
    }
}
