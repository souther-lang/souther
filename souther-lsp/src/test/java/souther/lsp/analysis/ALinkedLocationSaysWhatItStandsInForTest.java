package souther.lsp.analysis;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.lsp.protocol.LspDiagnostic;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An editor's linked location is a sentence about a place, and says what the place stands in for.
 *
 * <p>A warning about an edge no row is at points at the guard that drew it. Where the guard is one
 * of a body spliced in from a module this compile has no source for, the location it can be given
 * is the call in the reader's own file — so a link saying "the guard that draws that line" against
 * it says the guard is there, and it is not.
 *
 * <p>Here rather than only in the compiler's own fixture because this is a third renderer. The
 * terminal and the JSON a build reads both come from {@code souther-syntax}; an editor's related
 * information is assembled here, and it was the one surface that kept rendering a label and nothing
 * else after the other two had stopped. Nothing in the editor's own tests reads a link's message.
 */
class ALinkedLocationSaysWhatItStandsInForTest {

    private static final String URI = "file:///abs.sou";

    /** {@code Int.abs} is written in the standard library, which no compile has a source for. Its
     *  fork draws lines on {@code n} that the one row is not at, and the warning about them points
     *  at the guard — which here is a copy, stamped with the call on line 7. */
    private static final String MODEL = """
            module demo

            data Size = Int

            behavior sized : (n: Int) -> Size
                constructs Size
            let sized (n) = Size(Int.abs(n))

            example sized
                | "a positive one" : (5) -> Size(5)
            """;

    private static List<LspDiagnostic.Related> linksOfTheEdgeWarning() {
        Analyzer analyzer = new Analyzer();
        analyzer.measure(Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        Map<String, List<LspDiagnostic>> byUri =
                analyzer.diagnostics(ModuleGraph.of(Map.of(URI, MODEL)));

        List<LspDiagnostic> edges = byUri.getOrDefault(URI, List.of()).stream()
                .filter(d -> "E1916".equals(d.code()))
                .filter(d -> !d.related().isEmpty())
                .toList();
        assertFalse(edges.isEmpty(), () -> "an edge no row is at links to its guard: " + byUri);
        return edges.get(0).related();
    }

    @Test
    void aLinkIntoACopiedBodySaysWhereTheCodeIs() {
        for (LspDiagnostic.Related link : linksOfTheEdgeWarning()) {
            assertTrue(link.message().contains("`Int.abs`"),
                    () -> "the link says what the place it points at stands in for: "
                            + link.message());
        }
    }

    /** And it is still a link the editor can open: where the code is written is not where a reader
     *  can be sent, and the range is the call this compile has a file for. */
    @Test
    void theLinkStillPointsSomewhereTheEditorCanOpen() {
        for (LspDiagnostic.Related link : linksOfTheEdgeWarning()) {
            assertEquals(URI, link.uri());
            assertEquals(6, link.range().start().line(), "the call, as the editor counts lines");
        }
    }
}
