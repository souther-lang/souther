package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.LspDiagnostic;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the editor is told about a name on an import list that nothing below writes.
 *
 * <p>Listing it is not enough. A reader looking at an import line has no way to tell which of the
 * names on it earns its place, and the answer is worth having at a glance — so the diagnostic carries
 * the {@code Unnecessary} tag, which fades the text, and its range covers the one name rather than
 * the line the names share.
 */
class AnUnusedImportFadesInTheEditorTest {

    private static final String STOCK_URI = "file:///stock.sou";
    private static final String PICKING_URI = "file:///picking.sou";

    private static final String STOCK = """
            module probe.stock exposing ( StockLine, Sku )

            data Sku = String
                invariant String.length(value) >= 1

            data StockLine = { sku: Sku, quantity: Int }
            """;

    /** `StockLine` is on the list and nothing below says it. */
    private static final String PICKING = """
            module probe.picking

            import probe.stock ( Sku, StockLine )

            data Pick = { sku: Sku }
            """;

    private static List<LspDiagnostic> onPicking() {
        Map<String, List<LspDiagnostic>> byUri = new Analyzer()
                .diagnostics(ModuleGraph.of(Map.of(STOCK_URI, STOCK, PICKING_URI, PICKING)));
        return byUri.getOrDefault(PICKING_URI, List.of());
    }

    @Test
    void theRangeCoversTheNameAndNotTheLine() {
        List<LspDiagnostic> here = onPicking();

        assertEquals(1, here.size(), "one name is unused, so one marker: " + here);
        LspDiagnostic unused = here.get(0);
        assertEquals("E1922", unused.code());
        assertEquals(2, unused.range().start().line(), "the import line, zero-based");
        assertEquals(26, unused.range().start().character(), "`StockLine` starts here");
        assertEquals(35, unused.range().end().character(), "and ends after its last letter");
    }

    @Test
    void itIsAWarningAndFades() {
        LspDiagnostic unused = onPicking().get(0);

        assertEquals(LspDiagnostic.WARNING, unused.severity(), "it does not stop a build");
        assertEquals(List.of(LspDiagnostic.UNNECESSARY), unused.tags());
    }

    /** Nothing else gets the tag: an error about the same import list is not text that does nothing. */
    @Test
    void anImportThatIsWrongRatherThanUnusedIsNotFaded() {
        Map<String, List<LspDiagnostic>> byUri = new Analyzer()
                .diagnostics(ModuleGraph.of(Map.of(STOCK_URI, STOCK, PICKING_URI, """
                        module probe.picking

                        import probe.stock ( Sku, NotExposed )

                        data Pick = { sku: Sku }
                        """)));
        List<LspDiagnostic> here = byUri.getOrDefault(PICKING_URI, List.of());

        assertTrue(here.stream().noneMatch(d -> d.tags().contains(LspDiagnostic.UNNECESSARY)),
                "nothing here is faded: " + here);
        assertTrue(here.stream().anyMatch(d -> d.severity() == LspDiagnostic.ERROR),
                "and the import itself is still reported: " + here);
    }
}
