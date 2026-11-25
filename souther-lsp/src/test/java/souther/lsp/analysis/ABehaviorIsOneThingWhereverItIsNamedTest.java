package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import souther.compiler.ACompiledModel;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.lsp.protocol.Hover;
import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;
import souther.lsp.protocol.TextEdit;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A behavior is named in many places — its {@code behavior} and {@code let} lines, a
 * {@code depends on}, an {@code exposing} list, another module's import list, and in an attached
 * file an {@code example} header, a {@code fake} header and the left of a {@code with}. Whichever of
 * them the cursor is on, it is one behavior: a hover shows its declaration, a definition goes
 * there, and a rename rewrites one set of places. All three ask the compiler what the name denotes,
 * so where the question is asked from changes nothing.
 *
 * <p>The rest is what a match on spelling gets wrong: another module declaring {@code find} with
 * another signature, a parameter spelled like a behavior, and an {@code example} of a behavior an
 * import brings in, which names nothing. A file the compile cannot read is where spelling is all
 * there is, and a rename asked where the compiler answers still reaches it.
 *
 * <p>Every question about the workspace is asked of one analyzer, so it is compiled once. Nothing
 * here needs a row run, and no diagnose is asked for.
 */
class ABehaviorIsOneThingWhereverItIsNamedTest {

    private static final String MODEL_URI = "file:///m.sou";
    private static final String ATTACHED_URI = "file:///m.examples.sou";
    private static final String USER_URI = "file:///user.sou";
    private static final String OTHER_URI = "file:///other.sou";
    private static final String BROKEN_URI = "file:///broken.sou";

    private static final String MODEL = """
            module m exposing ( D, find, f )

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
            """;

    private static final String USER = """
            module user

            import m ( find )
            """;

    /** A file the compile cannot read, which goes on naming `find` all the same. */
    private static final String BROKEN = """
            module broken

            import m ( find )

            let g (d) = find(d)

            let unfinished =
            """;

    /** `find` spelled as one of `m`'s and declared otherwise, and `stamp`, which `n` imports. */
    private static final String OTHER = """
            module other exposing ( stamp )

            behavior find : (n: Int) -> Int

            let find (n) = n

            behavior stamp : (n: Int) -> Int

            let stamp (n) = n
            """;

    private static final Map<String, String> TEXTS = texts();

    private static final ModuleGraph GRAPH = ModuleGraph.of(TEXTS);

    private static final Analyzer ANALYZER = new Analyzer();

    private static Map<String, String> texts() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(MODEL_URI, MODEL);
        sources.put(ATTACHED_URI, ATTACHED);
        sources.put(USER_URI, USER);
        sources.put(OTHER_URI, OTHER);
        sources.put(BROKEN_URI, BROKEN);
        return sources;
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
    record Named(String uri, String marked, String declaration) {

        String text() {
            return TEXTS.get(uri);
        }

        Position cursor() {
            return at(text(), marked);
        }

        @Override
        public String toString() {
            return uri.substring(uri.lastIndexOf('/') + 1) + ": " + marked;
        }
    }

    private static final String FIND = "behavior [find] : (d: D) -> D";
    private static final String LOOK = "behavior [look] : (d: D) -> D";
    private static final String F = "behavior [f] : (d: D) -> D";

    /** One place for each way the compiler answers what a behavior's name is. */
    static Stream<Named> oneOfEachWayANameIsAnswered() {
        return Stream.of(
                new Named(ATTACHED_URI, "example [f]", F),
                new Named(ATTACHED_URI, "fake [find]", FIND),
                new Named(ATTACHED_URI, "with [look] =", LOOK),
                new Named(MODEL_URI, "behavior [f] : (d: D) -> D", F),
                new Named(MODEL_URI, "let [f] (d, find, look)", F),
                new Named(MODEL_URI, "exposing ( D, [find], f )", FIND),
                new Named(USER_URI, "import m ( [find] )", FIND));
    }

    /** Definition goes to the {@code behavior} line, and hover shows that line over the name the
     *  cursor is on. */
    @ParameterizedTest
    @MethodSource("oneOfEachWayANameIsAnswered")
    void definitionAndHoverAreTheBehaviorLine(Named named) {
        Location found = ANALYZER.definition(named.uri(), named.cursor(), GRAPH).orElseThrow();
        Hover shown = ANALYZER.hover(named.uri(), named.text(), named.cursor(), GRAPH)
                .orElseThrow();

        assertEquals(MODEL_URI, found.uri());
        assertEquals(named.declaration(), marked(MODEL, found.range()));
        String declaration = named.declaration().replace("[", "").replace("]", "");
        assertEquals("```souther\n" + declaration + "\n```", shown.contents());
        assertEquals(named.cursor(), shown.range().start(), "over the name under the cursor");
    }

    /** Every place a rename of `find` rewrites, once each — the parameter `let f` is injected with
     *  it through and the body's use of that, which must go on being spelled as the behavior; not
     *  `other`'s `find`, being another thing; and in the file the compile cannot read, what its
     *  spelling there names. */
    private static final List<String> FIND_IS_WRITTEN = List.of(
            "broken.sou: import m ( [find] )",
            "broken.sou: let g (d) = [find](d)",
            "m.examples.sou: fake [find]",
            "m.sou:     depends on [find], look",
            "m.sou: behavior [find] : (d: D) -> D",
            "m.sou: let f (d, [find], look) = look(find(d))",
            "m.sou: let f (d, find, look) = look([find](d))",
            "m.sou: module m exposing ( D, [find], f )",
            "user.sou: import m ( [find] )");

    /** Every place a rename of `f` rewrites, once each — not the parameter `echo` takes. */
    private static final List<String> F_IS_WRITTEN = List.of(
            "m.examples.sou: example [f]",
            "m.sou: behavior [f] : (d: D) -> D",
            "m.sou: let [f] (d, find, look) = look(find(d))",
            "m.sou: module m exposing ( D, find, [f] )");

    record Renamed(Named from, List<String> rewrites) {

        @Override
        public String toString() {
            return from.toString();
        }
    }

    static Stream<Renamed> placesARenameIsAskedFrom() {
        return Stream.of(
                new Renamed(new Named(MODEL_URI, "behavior [find] : (d: D) -> D", FIND),
                        FIND_IS_WRITTEN),
                new Renamed(new Named(MODEL_URI, "depends on [find], look", FIND), FIND_IS_WRITTEN),
                new Renamed(new Named(ATTACHED_URI, "fake [find]", FIND), FIND_IS_WRITTEN),
                new Renamed(new Named(MODEL_URI, "exposing ( D, [find], f )", FIND),
                        FIND_IS_WRITTEN),
                new Renamed(new Named(USER_URI, "import m ( [find] )", FIND), FIND_IS_WRITTEN),
                new Renamed(new Named(MODEL_URI, "= look([find](d))", FIND), FIND_IS_WRITTEN),
                new Renamed(new Named(ATTACHED_URI, "example [f]", F), F_IS_WRITTEN),
                new Renamed(new Named(MODEL_URI, "let [f] (d, find, look)", F), F_IS_WRITTEN));
    }

    /** What a rename rewrites is one set, whichever of the places naming the behavior it is asked
     *  from — the lists in a header among them — and no place is rewritten twice. */
    @ParameterizedTest
    @MethodSource("placesARenameIsAskedFrom")
    void aRenameRewritesOneSetWhereverItIsAskedFrom(Renamed renamed) {
        Named from = renamed.from();
        Map<String, List<TextEdit>> edits =
                ANALYZER.renameEdits(from.uri(), from.cursor(), GRAPH, "renamed");

        List<String> rewrites = new ArrayList<>();
        edits.forEach((uri, made) -> made.forEach(edit -> rewrites.add(
                uri.substring(uri.lastIndexOf('/') + 1) + ": "
                        + marked(TEXTS.get(uri), edit.range()))));
        rewrites.sort(null);
        assertEquals(renamed.rewrites(), rewrites);
    }

    /**
     * The edits a rename answers are what to write as well as where: written over the files the
     * compile read, they leave a workspace that compiles. One rename, because what it holds is how
     * an edit is made, which every rename shares; which places a rename reaches is the test above.
     */
    @Test
    void aRenameWrittenOverTheWorkspaceLeavesItCompiling() {
        Map<String, List<TextEdit>> edits = ANALYZER.renameEdits(USER_URI,
                at(USER, "import m ( [find] )"), GRAPH, "seek");

        Map<String, String> renamed = new LinkedHashMap<>();
        for (String uri : List.of(MODEL_URI, ATTACHED_URI, USER_URI, OTHER_URI)) {
            renamed.put(uri, applied(TEXTS.get(uri), edits.getOrDefault(uri, List.of())));
        }

        ACompiledModel.compiles(Compilation.ofDocuments(renamed, Set.of(), ModulePath.EMPTY));
        assertEquals("fake seek", renamed.get(ATTACHED_URI).lines().toList().get(2));
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
        String importing = """
                module n

                import other ( stamp )

                example stamp
                    | (1) -> 1
                """;
        String uri = "file:///n.sou";
        ModuleGraph graph = ModuleGraph.of(Map.of(uri, importing, OTHER_URI, OTHER));
        Analyzer analyzer = new Analyzer();
        Position target = at(importing, "example [stamp]");

        assertEquals(Optional.empty(), analyzer.definition(uri, target, graph));
        assertEquals("```souther\nstamp\n```",
                analyzer.hover(uri, importing, target, graph).orElseThrow().contents());
    }
}
