package souther.lsp.analysis;

import souther.lsp.protocol.Location;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.TextEdit;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name is one name however it is spelled, and it still occupies the characters the author typed.
 *
 * <p>Two spellings Unicode calls canonically equivalent are one name, so a reference written one way
 * reaches a declaration written the other. That is about identity. Where the name sits in the file is
 * a different question with a different answer: the characters are the ones on disk, and a decomposed
 * spelling is longer than the composed name it denotes. An editor asks both questions of the same
 * name, and answering the second one with the first one's string puts every range short.
 *
 * <p>The spellings are written as escapes on purpose. A composed and a decomposed kana look the same
 * in an editor, and a fixture that says which one it means only in its glyphs is a fixture that gets
 * silently normalized by whatever last saved the file.
 */
class ANameKeepsTheSpellingItWasWrittenWithTest {

    /** KATAKANA-HIRAGANA VOICED SOUND MARK, the combining half of the pair below. */
    private static final int VOICED = 0x3099;

    /** A hiragana ka followed by a combining voiced sound mark - two UTF-16 units. */
    private static final String NFD = of(0x304b, VOICED);
    /** The same kana as one code point. */
    private static final String NFC = of(0x304c);
    /** The combining mark on its own, for asking whether one was left behind. */
    private static final String COMBINING = of(VOICED);

    /** A + combining ring + combining acute - three UTF-16 units for one composed letter. */
    private static final String WIDE_NFD = of(0x0041, 0x030a, 0x0301);
    /** The same letter as one code point. */
    private static final String WIDE_NFC = of(0x01fa);

    /** A spelling written as the code points it is. A composed and a decomposed kana are the same
     * glyph, so a fixture that says which one it means only in its glyphs means whatever the last
     * thing to save the file decided it meant. */
    private static String of(int... codePoints) {
        return new String(codePoints, 0, codePoints.length);
    }

    private static ModuleGraph graphOf(Map<String, String> sources) {
        return ModuleGraph.of(new LinkedHashMap<>(sources));
    }

    /**
     * The position {@code offset} units past where {@code needle} starts in {@code text}, as an
     * editor counts. Written this way so a fixture's columns are read off the fixture rather than
     * counted by hand, which no one can check.
     */
    private static Position after(String text, String needle, int offset) {
        int index = text.indexOf(needle);
        assertTrue(index >= 0, "the fixture does not contain " + escape(needle));
        int lineStart = text.lastIndexOf('\n', index - 1) + 1;
        int line = (int) text.substring(0, index).chars().filter(c -> c == '\n').count();
        return new Position(line, index - lineStart + offset);
    }

    private static String escape(String s) {
        StringBuilder sb = new StringBuilder();
        s.codePoints().forEach(c -> sb.append(String.format("\\u%04x", c)));
        return sb.toString();
    }

    @Test
    void theTwoSpellingsAreDifferentStringsOfDifferentLengths() {
        // The premise. Nothing below means anything if a pair is already equal or the same width.
        assertTrue(!NFD.equals(NFC));
        assertEquals(2, NFD.length());
        assertEquals(1, NFC.length());
        assertTrue(!WIDE_NFD.equals(WIDE_NFC));
        assertEquals(3, WIDE_NFD.length());
        assertEquals(1, WIDE_NFC.length());
    }

    @Test
    void aComposedReferenceGoesToADecomposedDeclaration() {
        String up = "module up exposing ( " + NFD + " )\n\ndata " + NFD + " = Int\n";
        String here = "module here\n\ndata Box = { v: up." + NFC + " }\n";
        Map<String, String> sources = Map.of("file:///up.sou", up, "file:///here.sou", here);

        Optional<Location> found = new Analyzer()
                .definition("file:///here.sou", after(here, "up." + NFC, 3), graphOf(sources));

        assertTrue(found.isPresent(), "the reference and the declaration are one name");
        assertEquals("file:///up.sou", found.get().uri());
    }

    @Test
    void renamingADecomposedDeclarationCoversTheWholeSpelling() {
        String source = "module demo exposing ( " + NFD + " )\n\ndata " + NFD
                + " = Int\n\ndata Box = { v: " + NFC + " }\n";
        Map<String, String> sources = Map.of("file:///demo.sou", source);

        Map<String, List<TextEdit>> edits = new Analyzer().renameEdits(
                "file:///demo.sou", after(source, "data " + NFD, 5), graphOf(sources), "Renamed");

        String rewritten = apply(source, edits.get("file:///demo.sou"));
        assertTrue(!rewritten.contains(COMBINING),
                "a combining mark was left behind: " + escape(rewritten));
    }

    @Test
    void aCursorPastWhereTheComposedNameWouldEndIsStillOnTheName() {
        // The declaration is three units wide and denotes a one-unit name. A cursor on its last unit
        // is inside what the author typed and outside what the name is spelled.
        String source = "module demo exposing ( " + WIDE_NFD + " )\n\ndata " + WIDE_NFD + " = Int\n";
        Map<String, String> sources = Map.of("file:///demo.sou", source);
        Position lastUnit = after(source, "data " + WIDE_NFD, 5 + WIDE_NFD.length() - 1);

        Optional<Location> found =
                new Analyzer().definition("file:///demo.sou", lastUnit, graphOf(sources));

        assertTrue(found.isPresent(), "the cursor is on the third unit of a three-unit name");
    }

    /**
     * Both spellings are the same name, so both are references to it — and each covers the
     * characters it was written with, which is one more for the decomposed one.
     *
     * <p>The {@code exposing} entry is not among them: find-references answers about uses, and the
     * binding sites are {@code renamingADecomposedDeclarationCoversTheWholeSpelling}'s.
     */
    @Test
    void referencesFindBothSpellingsAndCoverWhatEachIsWrittenWith() {
        String source = "module demo exposing ( " + NFD + " )\n\ndata " + NFD
                + " = Int\n\ndata A = { v: " + NFC + " }\n\ndata B = { v: " + NFD + " }\n";
        Map<String, String> sources = Map.of("file:///demo.sou", source);

        List<Location> found = new Analyzer().references("file:///demo.sou",
                after(source, "data " + NFD, 5), graphOf(sources), true);

        assertEquals(3, found.size(), "the declaration and both uses: " + found);
        assertEquals(List.of(2, 1, 2), found.stream().map(ANameKeepsTheSpellingItWasWrittenWithTest::width).toList(),
                "the decomposed declaration, the composed use, the decomposed use: " + found);
    }

    /** How many characters a location covers. Every one of these is on one line. */
    private static int width(Location at) {
        return at.range().end().character() - at.range().start().character();
    }

    /**
     * Every kind of name the author declares, each written decomposed and used composed.
     *
     * <p>Not one case standing for the rest: a behavior, a helper and a {@code let} binding are each
     * declared by a different node, and the occurrence has to reach each of them. A test over one
     * declaration passes while the others answer from a name the source does not spell — which is
     * what this branch shipped.
     *
     * <p>A field is not here. An editor is deliberately not told what a field read is, because a
     * rename answered from one would rewrite the declaration and none of the reads the type
     * settles; that the compiler answers where a field is declared, across spellings, is
     * {@code ResolvedValueNamesTest}'s.
     */
    @Test
    void aBehaviorAHelperAndALocalAreEachFoundFromTheOtherSpelling() {
        // one decomposed name per kind, each told apart by an ASCII tail so that a fixture with
        // four names does not accidentally have one
        String field = NFD + "f";
        String behavior = NFD + "b";
        String helper = NFD + "h";
        String local = NFD + "l";
        String source = "module demo exposing ( Box, " + behavior + " )\n"
                + "\n"
                + "data Box = { " + field + ": Int }\n"
                + "\n"
                + "behavior " + behavior + " : (b: Box) -> Int\n"
                + "\n"
                + "let " + behavior + " (b) = {\n"
                + "    let " + local + " = " + compose(helper) + "(b." + compose(field) + ")\n"
                + "    " + compose(local) + "\n"
                + "}\n"
                + "\n"
                + "let " + helper + " (n: Int) : Int = n\n"
                + "\n"
                + "behavior caller : (b: Box) -> Int depends on " + compose(behavior) + "\n";
        Map<String, String> sources = Map.of("file:///demo.sou", source);
        ModuleGraph graph = graphOf(sources);

        assertDefinable(graph, source, "= " + compose(helper), 2, helper,
                "the helper the body applies");
        assertDefinable(graph, source, "    " + compose(local) + "\n}", 4, local,
                "the local the block binds");
        assertDefinable(graph, source, "depends on " + compose(behavior), 11, behavior,
                "the behavior another one depends on");
    }

    /**
     * A qualifier that composes to fewer characters than it was written with moves where the last
     * segment starts, and a rename rewrites the last segment only.
     *
     * <p>Counting that boundary in the name rather than in the spelling puts the rewrite one
     * character inside the qualifier: the module keeps a stray combining mark and stops naming the
     * module it named.
     */
    @Test
    void aRenameThroughADecomposedQualifierRewritesTheLastSegmentOnly() {
        String module = NFD + "m";
        String up = "module " + module + " exposing ( Amount )\n\ndata Amount = Int\n";
        String here = "module here\n\ndata Box = { v: " + module + ".Amount }\n";
        Map<String, String> sources = Map.of("file:///up.sou", up, "file:///here.sou", here);

        Map<String, List<TextEdit>> edits = new Analyzer().renameEdits("file:///here.sou",
                after(here, module + ".Amount", module.length() + 1), graphOf(sources), "Renamed");

        String rewritten = apply(here, edits.get("file:///here.sou"));
        assertEquals("module here\n\ndata Box = { v: " + module + ".Renamed }\n", rewritten,
                "the qualifier was rewritten along with the name: " + escape(rewritten));
    }

    /**
     * A qualified name is read over meaningful tokens, so its parts need not be adjacent — and where
     * the last one is written is the only thing a rename may rewrite.
     *
     * <p>Nothing in the joined spelling `up.Amount` says how far apart the parts are. Counting the
     * last segment's start in it puts a rename on the dot for `up . Amount`, and on the wrong line
     * for a name a comment carries over a line break. Both parse; the second is how an author
     * annotates which module they meant.
     */
    @Test
    void aQualifiedNameIsRenamedWhereItsLastPartIsWrittenHoweverFarApartTheyAre() {
        String up = "module up exposing ( Amount )\n\ndata Amount = Int\n";
        for (String reference : List.of("up.Amount", "up . Amount",
                "up // which module\n    . Amount")) {
            String here = "module here\n\ndata Box = { v: " + reference + " }\n";
            Map<String, String> sources =
                    Map.of("file:///up.sou", up, "file:///here.sou", here);

            Map<String, List<TextEdit>> edits = new Analyzer().renameEdits("file:///here.sou",
                    after(here, "Amount }", 0), graphOf(sources), "Renamed");

            assertEquals(here.replace("Amount }", "Renamed }"),
                    apply(here, edits.get("file:///here.sou")),
                    "renaming through `" + reference.replace("\n", "\\n") + "`");
        }
    }

    /**
     * A name is the characters that spell it, not the stretch of file they lie in.
     *
     * <p>A qualified name may be written with a comment and a line break between its parts, and a
     * report underlines all of it because an underline with holes in it is not something to read.
     * A cursor is a different question: it is on the name only where a token is. Answering the
     * second with the first put go-to-definition, and with it rename, under a cursor in the middle
     * of a comment — a rename of a type across the workspace, started from prose.
     */
    @Test
    void aCursorIsOnAQualifiedNameOnlyWhereOneOfItsPartsIsWritten() {
        String up = "module up exposing ( Amount )\n\ndata Amount = Int\n";
        String here = "module here\n\ndata Box = { v: up // which module\n        . Amount }\n";
        Map<String, String> sources = Map.of("file:///up.sou", up, "file:///here.sou", here);
        ModuleGraph graph = graphOf(sources);

        for (Position on : List.of(after(here, "up //", 0), after(here, "up //", 1),
                after(here, "Amount }", 0), after(here, "Amount }", 5))) {
            assertTrue(new Analyzer().definition("file:///here.sou", on, graph).isPresent(),
                    "a part of the name is written at " + on);
        }
        for (Position off : List.of(after(here, "// which", 0), after(here, "which", 2),
                after(here, "        . Amount", 0), after(here, "        . Amount", 4),
                after(here, "        . Amount", 8), after(here, "        . Amount", 9))) {
            assertTrue(new Analyzer().definition("file:///here.sou", off, graph).isEmpty(),
                    "nothing of the name is written at " + off);
            assertTrue(new Analyzer().renameEdits("file:///here.sou", off, graph, "R").isEmpty(),
                    "a rename started where no name is written at " + off);
        }
    }

    /** The composed spelling of a decomposed name — what the same name looks like typed the other
     *  way. */
    private static String compose(String decomposed) {
        return java.text.Normalizer.normalize(decomposed, java.text.Normalizer.Form.NFC);
    }

    /** Asserts that the name {@code offset} units into {@code needle} is one an editor can open. */
    private static void assertDefinable(ModuleGraph graph, String source, String needle, int offset,
                                        String declared, String what) {
        Position at = after(source, needle, offset);
        Optional<Location> found = new Analyzer().definition("file:///demo.sou", at, graph);
        assertTrue(found.isPresent(), what + " is not reachable from a composed spelling at " + at);
        assertEquals(declared.length(), found.get().range().end().character()
                        - found.get().range().start().character(),
                what + " is declared decomposed, so its declaration is that many characters wide");
    }

    /** Applies edits back to front so an earlier one does not move a later one. */
    private static String apply(String text, List<TextEdit> edits) {
        assertTrue(edits != null && !edits.isEmpty(), "nothing to apply");
        List<TextEdit> ordered = edits.stream()
                .sorted((a, b) -> compare(b.range().start(), a.range().start())).toList();
        StringBuilder sb = new StringBuilder(text);
        for (TextEdit edit : ordered) {
            sb.replace(offset(text, edit.range().start()), offset(text, edit.range().end()),
                    edit.newText());
        }
        return sb.toString();
    }

    private static int compare(Position a, Position b) {
        return a.line() != b.line() ? Integer.compare(a.line(), b.line())
                : Integer.compare(a.character(), b.character());
    }

    private static int offset(String text, Position pos) {
        int offset = 0;
        for (int line = 0; line < pos.line(); line++) {
            offset = text.indexOf('\n', offset) + 1;
        }
        return offset + pos.character();
    }
}
