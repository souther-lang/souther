package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Widening a selection takes in the next thing the author wrote around what is selected, which is
 * the nesting the parser already built. Nothing here asks what a name means.
 */
class WideningASelectionTakesInTheNextThingWrittenAroundItTest {

    private static final String URI = "file:///m.sou";

    private static final String MODEL = """
            module m

            data D = { v: Int }

            behavior f : (d: D) -> Int
            let f (d) = if d.v > 0 then d.v else 0
            """;

    @Test
    void itBeginsAtTheThingUnderTheCursorAndEachStepContainsTheOneBefore() {
        // on the `v` of the first `d.v`
        List<Range> widening = widening(at(5, 18));

        assertFalse(widening.isEmpty(), "the cursor is on a token");
        assertEquals(1, widening.getFirst().end().character() - widening.getFirst().start().character(),
                "the innermost is the one-character name it is on");
        for (int i = 1; i < widening.size(); i++) {
            assertTrue(contains(widening.get(i), widening.get(i - 1)),
                    widening.get(i) + " does not take in " + widening.get(i - 1));
        }
    }

    @Test
    void itEndsAtTheWholeFile() {
        List<Range> widening = widening(at(5, 18));
        Range widest = widening.getLast();

        assertEquals(0, widest.start().line());
        assertEquals(0, widest.start().character());
    }

    @Test
    void noStepTakesInNothing() {
        List<Range> widening = widening(at(5, 18));

        for (int i = 1; i < widening.size(); i++) {
            assertFalse(widening.get(i).equals(widening.get(i - 1)),
                    "a step that widens by nothing is a keystroke that did nothing");
        }
    }

    /** And a document that will not compile widens the same way, the question never having been
     *  about meaning. */
    @Test
    void aDocumentThatDoesNotCompileWidensAllTheSame() {
        String broken = """
                module m

                behavior f : (d: NoSuchType) -> Int
                let f (d) = d.missing
                """;

        assertFalse(widening(broken, at(3, 14)).isEmpty());
    }

    private static boolean contains(Range outer, Range inner) {
        return !after(outer.start(), inner.start()) && !after(inner.end(), outer.end());
    }

    private static boolean after(Position a, Position b) {
        return a.line() != b.line() ? a.line() > b.line() : a.character() > b.character();
    }

    private static Position at(int line, int character) {
        return new Position(line, character);
    }

    private static List<Range> widening(Position pos) {
        return widening(MODEL, pos);
    }

    private static List<Range> widening(String text, Position pos) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, text);
        ModuleGraph graph = ModuleGraph.of(sources);
        return new Analyzer().selectionRanges(URI, pos, graph);
    }
}
