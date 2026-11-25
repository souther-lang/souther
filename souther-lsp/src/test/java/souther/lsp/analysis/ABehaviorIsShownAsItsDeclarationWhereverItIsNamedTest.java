package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import souther.lsp.protocol.Hover;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Wherever a behavior is named — its own {@code behavior} and {@code let} lines, and in an attached
 * file an {@code example} header, a {@code fake} header and the left of a {@code with} — a hover
 * shows its declaration and a definition goes there, because both ask the compiler what the name
 * denotes. One place for each way the compiler answers a name.
 *
 * <p>The rest is what a match on spelling gets wrong: another module declaring {@code find} with
 * another signature, a parameter spelled like a behavior, and an {@code example} of a behavior an
 * import brings in, which names nothing.
 *
 * <p>Every question is asked of one workspace and one analyzer, so the workspace is compiled once.
 * Nothing here needs a row run, and no diagnose is asked for.
 */
class ABehaviorIsShownAsItsDeclarationWhereverItIsNamedTest {

    private static final String MODEL_URI = "file:///m.sou";
    private static final String ATTACHED_URI = "file:///m.examples.sou";
    private static final String OTHER_URI = "file:///other.sou";

    private static final String MODEL = """
            module m

            import other ( stamp )

            data D = { v: Int }

            behavior find : (d: D) -> D

            behavior look : (d: D) -> D

            behavior f : (d: D) -> D
                depends on find, look

            let f (d, find, look) = look(find(d))

            let echo (f: D): D = f
            """;

    private static final String ATTACHED = """
            examples for m

            fake find
                | _ -> D { v = 0 }

            example f
                | (D { v = 3 }) with look = D { v = 9 } -> D { v = 9 }

            example stamp
                | (1) -> 1
            """;

    /** `find` spelled as one of `m`'s and declared otherwise, and `stamp`, which `m` imports. */
    private static final String OTHER = """
            module other exposing ( stamp )

            behavior find : (n: Int) -> Int

            let find (n) = n

            behavior stamp : (n: Int) -> Int

            let stamp (n) = n
            """;

    private static final ModuleGraph GRAPH = graph();

    private static final Analyzer ANALYZER = new Analyzer();

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(MODEL_URI, MODEL);
        sources.put(ATTACHED_URI, ATTACHED);
        sources.put(OTHER_URI, OTHER);
        return ModuleGraph.of(sources);
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

    static Stream<Named> oneOfEachWayANameIsAnswered() {
        return Stream.of(
                new Named(ATTACHED_URI, ATTACHED, "example [f]", "behavior [f] : (d: D) -> D"),
                new Named(ATTACHED_URI, ATTACHED, "fake [find]", "behavior [find] : (d: D) -> D"),
                new Named(ATTACHED_URI, ATTACHED, "with [look] =", "behavior [look] : (d: D) -> D"),
                new Named(MODEL_URI, MODEL, "behavior [f] : (d: D) -> D",
                        "behavior [f] : (d: D) -> D"),
                new Named(MODEL_URI, MODEL, "let [f] (d, find, look)",
                        "behavior [f] : (d: D) -> D"));
    }

    /** Definition goes to the {@code behavior} line, and hover shows that line over the name the
     *  cursor is on. */
    @ParameterizedTest
    @MethodSource("oneOfEachWayANameIsAnswered")
    void definitionAndHoverAreTheBehaviorLine(Named named) {
        Position cursor = at(named.text(), named.marked());

        Location found = ANALYZER.definition(named.uri(), cursor, GRAPH).orElseThrow();
        Hover shown = ANALYZER.hover(named.uri(), named.text(), cursor, GRAPH).orElseThrow();

        assertEquals(MODEL_URI, found.uri());
        assertEquals(named.declaration(), marked(MODEL, found.range()));
        String declaration = named.declaration().replace("[", "").replace("]", "");
        assertEquals("```souther\n" + declaration + "\n```", shown.contents());
        assertTrue(marked(named.text(), shown.range()).contains(named.marked()),
                marked(named.text(), shown.range()));
    }

    @Test
    void aParameterSpelledLikeABehaviorIsTheParameter() {
        Position use = at(MODEL, "let echo (f: D): D = [f]");

        Location found = ANALYZER.definition(MODEL_URI, use, GRAPH).orElseThrow();
        Hover shown = ANALYZER.hover(MODEL_URI, MODEL, use, GRAPH).orElseThrow();

        assertEquals("let echo ([f]: D): D = f", marked(MODEL, found.range()));
        assertEquals("```souther\nf: D\n```", shown.contents());
    }

    /**
     * An {@code example} is about a behavior of its own module (spec
     * §example-target-is-a-behavior), so a name an import brings in is no target. The compile says
     * it names nothing here, and an editor that went to the imported declaration would be saying
     * the rows are about that one.
     */
    @Test
    void anExampleOfAnImportedBehaviorNamesNothing() {
        Position target = at(ATTACHED, "example [stamp]");

        assertEquals(Optional.empty(), ANALYZER.definition(ATTACHED_URI, target, GRAPH));
        assertEquals("```souther\nstamp\n```",
                ANALYZER.hover(ATTACHED_URI, ATTACHED, target, GRAPH).orElseThrow().contents());
    }

    @Test
    void findingReferencesFromTheBehaviorLineReachesTheExampleHeader() {
        List<Location> found = ANALYZER.references(MODEL_URI,
                at(MODEL, "behavior [f] : (d: D) -> D"), GRAPH, false);

        List<String> shown = new ArrayList<>();
        for (Location each : found) {
            shown.add(each.uri().substring(each.uri().lastIndexOf('/') + 1) + ": "
                    + marked(each.uri().equals(MODEL_URI) ? MODEL : ATTACHED, each.range()));
        }
        assertTrue(shown.contains("m.examples.sou: example [f]"), shown.toString());
        assertFalse(shown.contains("m.sou: let echo (f: D): D = [f]"),
                "the parameter is not the behavior: " + shown);
    }
}
