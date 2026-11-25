package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import souther.lsp.protocol.Hover;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.LspDiagnostic;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;
import souther.lsp.protocol.TextEdit;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior is named in many places — its own {@code behavior} and {@code let} lines, a
 * {@code depends on}, a composition's stages, an {@code example} header, a {@code fake} header, the
 * left of a {@code with} — and in more than one file. Wherever it is named, a hover shows its
 * declaration and a definition goes there, and the two agree because both ask the compiler what the
 * name denotes.
 *
 * <p>Two things here are what a match on spelling gets wrong. Another module declares a behavior of
 * the same name with another signature, and a helper takes a parameter spelled like a behavior of
 * this module.
 */
class ABehaviorIsShownAsItsDeclarationWhereverItIsNamedTest {

    private static final String MODEL_URI = "file:///m.sou";
    private static final String ATTACHED_URI = "file:///m.examples.sou";
    private static final String OTHER_URI = "file:///other.sou";

    private static final String MODEL = """
            module m

            data D = { v: Int }

            behavior find : (d: D) -> D

            behavior look : (d: D) -> D

            behavior f : (d: D) -> D
                depends on find, look

            let f (d, find, look) = look(find(d))

            behavior twice = f >-> f

            let echo (f: D): D = f

            example f
                | "inline" : (D { v = 1 }) with look = D { v = 9 } -> D { v = 9 }
            """;

    private static final String ATTACHED = """
            examples for m

            fake find
                | (D { v = 1 }) -> D { v = 2 }
                | _ -> D { v = 0 }

            example f
                | "attached" : (D { v = 3 }) with look = D { v = 9 } -> D { v = 9 }
            """;

    /** Not imported by `m`: a behavior spelled like one of `m`'s and declared otherwise. */
    private static final String OTHER = """
            module other exposing ( find )

            behavior find : (n: Int) -> Int

            let find (n) = n
            """;

    private static final String FIND = "behavior [find] : (d: D) -> D";
    private static final String LOOK = "behavior [look] : (d: D) -> D";
    private static final String F = "behavior [f] : (d: D) -> D";

    private static ModuleGraph graph() {
        return ModuleGraph.of(sources(MODEL, ATTACHED));
    }

    private static Map<String, String> sources(String model, String attached) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(MODEL_URI, model);
        sources.put(ATTACHED_URI, attached);
        sources.put(OTHER_URI, OTHER);
        return sources;
    }

    private static Analyzer warmed(ModuleGraph graph) {
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);
        return analyzer;
    }

    /**
     * Where the name in brackets is, on the first line of {@code text} that reads as
     * {@code marked} does without them.
     */
    private static Position at(String text, String marked) {
        String plain = marked.replace("[", "").replace("]", "");
        List<String> lines = text.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            int column = lines.get(i).indexOf(plain);
            if (column >= 0) {
                return new Position(i, column + marked.indexOf('['));
            }
        }
        throw new AssertionError("no line reads `" + plain + "`");
    }

    /** The line of {@code text} the range is on, with the range marked by {@code [ ]}. */
    private static String marked(String text, Range range) {
        String line = text.lines().toList().get(range.start().line());
        return line.substring(0, range.start().character()) + "["
                + line.substring(range.start().character(), range.end().character()) + "]"
                + line.substring(range.end().character());
    }

    /** A place a behavior is named, and the line that declares it with the name marked. */
    record Named(String uri, String text, String marked, String declaration) {

        @Override
        public String toString() {
            return uri.substring(uri.lastIndexOf('/') + 1) + ": " + marked;
        }
    }

    static Stream<Named> everyPlaceABehaviorIsNamed() {
        return Stream.of(
                new Named(MODEL_URI, MODEL, "behavior [find] : (d: D) -> D", FIND),
                new Named(MODEL_URI, MODEL, "depends on [find], look", FIND),
                new Named(ATTACHED_URI, ATTACHED, "fake [find]", FIND),
                new Named(MODEL_URI, MODEL, "depends on find, [look]", LOOK),
                new Named(MODEL_URI, MODEL, "| \"inline\" : (D { v = 1 }) with [look] =", LOOK),
                new Named(ATTACHED_URI, ATTACHED, "| \"attached\" : (D { v = 3 }) with [look] =",
                        LOOK),
                new Named(MODEL_URI, MODEL, "behavior [f] : (d: D) -> D", F),
                new Named(MODEL_URI, MODEL, "let [f] (d, find, look)", F),
                new Named(MODEL_URI, MODEL, "behavior twice = [f] >-> f", F),
                new Named(MODEL_URI, MODEL, "behavior twice = f >-> [f]", F),
                new Named(MODEL_URI, MODEL, "example [f]", F),
                new Named(ATTACHED_URI, ATTACHED, "example [f]", F));
    }

    @Test
    void everyFileIsCleanSoNothingBelowIsAboutAFileThatDoesNotCompile() {
        Map<String, List<LspDiagnostic>> found = new Analyzer().diagnostics(graph());

        assertEquals(List.of(), found.get(MODEL_URI));
        assertEquals(List.of(), found.get(ATTACHED_URI));
        assertEquals(List.of(), found.get(OTHER_URI));
    }

    @ParameterizedTest
    @MethodSource("everyPlaceABehaviorIsNamed")
    void aDefinitionGoesToTheBehaviorLine(Named named) {
        ModuleGraph graph = graph();

        Location found = warmed(graph)
                .definition(named.uri(), at(named.text(), named.marked()), graph).orElseThrow();

        assertEquals(MODEL_URI, found.uri());
        assertEquals(named.declaration(), marked(MODEL, found.range()));
    }

    /** What is shown is the declaration, and what it is shown over is the name the cursor is on. */
    @ParameterizedTest
    @MethodSource("everyPlaceABehaviorIsNamed")
    void aHoverShowsTheBehaviorLineOverTheNameUnderTheCursor(Named named) {
        ModuleGraph graph = graph();

        Hover shown = warmed(graph).hover(named.uri(), named.text(),
                at(named.text(), named.marked()), graph).orElseThrow();

        String declaration = named.declaration().replace("[", "").replace("]", "");
        assertEquals("```souther\n" + declaration + "\n```", shown.contents());
        assertTrue(marked(named.text(), shown.range()).contains(named.marked()),
                marked(named.text(), shown.range()));
    }

    @Test
    void aParameterSpelledLikeABehaviorIsTheParameter() {
        ModuleGraph graph = graph();
        Position use = at(MODEL, "let echo (f: D): D = [f]");
        Analyzer analyzer = warmed(graph);

        Location found = analyzer.definition(MODEL_URI, use, graph).orElseThrow();
        Hover shown = analyzer.hover(MODEL_URI, MODEL, use, graph).orElseThrow();

        assertEquals("let echo ([f]: D): D = f", marked(MODEL, found.range()));
        assertEquals("```souther\nf: D\n```", shown.contents());
    }

    /**
     * An {@code example} is about a behavior of its own module (spec
     * §example-target-is-a-behavior), so a name an import brings in is no target, however it is
     * spelled. What the compile says of it is that it names nothing here, and an editor that went
     * to the imported declaration would be saying the rows are about that one.
     */
    @Test
    void anExampleOfAnImportedBehaviorNamesNothing() {
        String importing = """
                module n

                import other ( find )

                example find
                    | (1) -> 1
                """;
        String uri = "file:///n.sou";
        ModuleGraph graph = ModuleGraph.of(Map.of(uri, importing, OTHER_URI, OTHER));
        Analyzer analyzer = new Analyzer();
        Position target = at(importing, "example [find]");

        List<LspDiagnostic> said = analyzer.diagnostics(graph).get(uri);

        assertTrue(said.stream().anyMatch(d -> "E1901".equals(d.code())), said.toString());
        assertEquals(Optional.empty(), analyzer.definition(uri, target, graph));
        assertEquals("```souther\nfind\n```",
                analyzer.hover(uri, importing, target, graph).orElseThrow().contents());
    }

    @Test
    void findingReferencesFromTheBehaviorLineReachesEveryExampleHeader() {
        ModuleGraph graph = graph();

        List<Location> found = warmed(graph)
                .references(MODEL_URI, at(MODEL, "behavior [f] : (d: D) -> D"), graph, false);

        List<String> shown = new ArrayList<>();
        for (Location each : found) {
            shown.add(each.uri().substring(each.uri().lastIndexOf('/') + 1) + ": "
                    + marked(each.uri().equals(MODEL_URI) ? MODEL : ATTACHED, each.range()));
        }
        assertTrue(shown.contains("m.sou: example [f]"), shown.toString());
        assertTrue(shown.contains("m.examples.sou: example [f]"), shown.toString());
        assertFalse(shown.contains("m.sou: let echo (f: D): D = [f]"),
                "the parameter is not the behavior: " + shown);
    }

    @Test
    void renamingFromAnAttachedExampleHeaderLeavesBothFilesCompiling() {
        ModuleGraph graph = graph();

        Map<String, List<TextEdit>> edits = warmed(graph).renameEdits(ATTACHED_URI,
                at(ATTACHED, "example [f]"), graph, "renamed");

        String model = applied(MODEL, edits.getOrDefault(MODEL_URI, List.of()));
        String attached = applied(ATTACHED, edits.getOrDefault(ATTACHED_URI, List.of()));
        assertTrue(model.contains("behavior renamed : (d: D) -> D"), model);
        assertTrue(model.contains("let renamed (d, find, look)"), model);
        assertTrue(model.contains("behavior twice = renamed >-> renamed"), model);
        assertTrue(model.contains("example renamed"), model);
        assertTrue(model.contains("let echo (f: D): D = f"), model);
        assertTrue(attached.contains("example renamed"), attached);
        Map<String, List<LspDiagnostic>> after =
                new Analyzer().diagnostics(ModuleGraph.of(sources(model, attached)));
        assertEquals(List.of(), after.get(MODEL_URI));
        assertEquals(List.of(), after.get(ATTACHED_URI));
    }

    /** {@code text} with each edit written over its range, the last one first. */
    private static String applied(String text, List<TextEdit> edits) {
        List<String> lines = new ArrayList<>(text.lines().toList());
        List<TextEdit> lastFirst = new ArrayList<>(edits);
        lastFirst.sort(Comparator.comparing((TextEdit e) -> e.range().start().line())
                .thenComparing(e -> e.range().start().character()).reversed());
        for (TextEdit edit : lastFirst) {
            Range r = edit.range();
            String line = lines.get(r.start().line());
            lines.set(r.start().line(), line.substring(0, r.start().character()) + edit.newText()
                    + line.substring(r.end().character()));
        }
        return String.join("\n", lines) + "\n";
    }
}
