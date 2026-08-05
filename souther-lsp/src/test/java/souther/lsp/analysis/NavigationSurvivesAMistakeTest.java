package souther.lsp.analysis;

import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;
import souther.lsp.protocol.TextEdit;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Navigation keeps answering about a file that has a mistake somewhere else in it.
 *
 * <p>Half-finished is the normal state of a file in an editor. A compiler that answers only about
 * files with nothing wrong in them answers exactly when the author does not need it — and falling
 * back to matching the spelling is worse than not answering, because it silently does the wrong
 * thing: renaming a type rewrites the tail of a qualified reference to another module's type.
 */
class NavigationSurvivesAMistakeTest {

    private static final String UP = """
            module up exposing ( Amount )

            data Amount = Int
            """;

    /** Names up's Amount, declares one of its own — and names a type that does not exist. */
    private static final String HERE = """
            module here exposing ( Amount, Box )

            data Amount = String

            data Box = { far: up.Amount, near: Amount, oops: Nowhere }
            """;

    /** A hiragana ka followed by a combining voiced sound mark, and the same kana as one code point.
     *  Written as code points because the two are one glyph and a fixture that says which it means
     *  only in its glyphs means whatever last saved the file. */
    private static final String NFD = new String(new int[] {0x304b, 0x3099}, 0, 2);
    private static final String NFC = new String(new int[] {0x304c}, 0, 1);

    /**
     * A file the compiler could not read is answered about by matching what is written, and two
     * spellings Unicode calls equivalent are one name there too.
     *
     * <p>This is the state an editor spends most of its time in, and it was the one where the
     * equivalence stopped holding: the token being compared was canonicalized and the one under the
     * cursor was not, so a cursor on the decomposed spelling found nothing while a cursor on the
     * composed spelling found the declaration. Which of the two an author's cursor is on is not
     * something an editor may answer differently.
     */
    @Test
    void aBrokenFileStillAnswersAcrossTheTwoSpellings() {
        String source = "module demo\n\ndata " + NFC + " = Int\n\ndata Box = { value: " + NFD
                + " }\n\nlet unfinished (\n";
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///demo.sou", source);
        ModuleGraph graph = ModuleGraph.of(sources);
        Position onTheDecomposedUse = new Position(4, "data Box = { value: ".length());

        assertTrue(new Analyzer().definition("file:///demo.sou", onTheDecomposedUse, graph)
                        .isPresent(),
                "the use and the declaration are one name however each is spelled");
        assertEquals(2, new Analyzer()
                        .references("file:///demo.sou", onTheDecomposedUse, graph, true).size(),
                "the declaration and the one use");
        assertEquals("module demo\n\ndata R = Int\n\ndata Box = { value: R }\n\n"
                        + "let unfinished (\n",
                applied(source, new Analyzer().renameEdits("file:///demo.sou", onTheDecomposedUse,
                        graph, "R").get("file:///demo.sou")));
    }

    /**
     * A caret just past a name answers the same in a file the compiler could not read.
     *
     * <p>That boundary is where a caret rests when its author has just typed the name, and the two
     * paths were reading it differently — the compiler's answer counted it and the scan of
     * characters did not. Which of the two answers an author gets is not for whether the rest of
     * the file happens to parse to decide.
     */
    @Test
    void aCaretJustPastANameAnswersWhetherTheFileParsesOrNot() {
        String broken = "module demo\n\ndata D = Int\n\ndata Box = { value: D }\n\nlet held (\n";
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///demo.sou", broken);
        Position pastTheUse = new Position(4, "data Box = { value: D".length());

        assertTrue(new Analyzer().definition("file:///demo.sou", pastTheUse, ModuleGraph.of(sources))
                .isPresent(), "the caret rests just past `D`");
    }

    /** {@code edits} written back, latest first so an earlier one does not move a later one. */
    private static String applied(String text, List<TextEdit> edits) {
        StringBuilder sb = new StringBuilder(text);
        edits.stream()
                .sorted((a, b) -> b.range().start().line() != a.range().start().line()
                        ? Integer.compare(b.range().start().line(), a.range().start().line())
                        : Integer.compare(b.range().start().character(),
                                a.range().start().character()))
                .forEach(edit -> sb.replace(offset(text, edit.range().start()),
                        offset(text, edit.range().end()), edit.newText()));
        return sb.toString();
    }

    private static int offset(String text, Position pos) {
        int offset = 0;
        for (int line = 0; line < pos.line(); line++) {
            offset = text.indexOf('\n', offset) + 1;
        }
        return offset + pos.character();
    }

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///up.sou", UP);
        sources.put("file:///here.sou", HERE);
        return ModuleGraph.of(sources);
    }

    /** Where `data Amount = String` names itself, in here.sou. */
    private static final Position HERES_AMOUNT = new Position(2, 5);

    @Test
    void theMistakeItselfIsReported() {
        assertTrue(new Analyzer().diagnostics(graph()).get("file:///here.sou").stream()
                        .anyMatch(d -> d.message().contains("Nowhere")),
                "the name that denotes nothing is what the author is told about");
    }

    @Test
    void renamingIsStillAboutWhatNamesDenote() {
        Map<String, List<TextEdit>> edits = new Analyzer()
                .renameEdits("file:///here.sou", HERES_AMOUNT, graph(), "Renamed");

        assertTrue(edits.getOrDefault("file:///up.sou", List.of()).isEmpty(),
                "up declares an Amount of its own, which this rename is not about");
        assertEquals(3, edits.getOrDefault("file:///here.sou", List.of()).size(),
                "the declaration, the `exposing` entry and the one bare use — not the tail of"
                        + " `up.Amount`, mistake in the file or not");
    }
}
