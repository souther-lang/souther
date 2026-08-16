package souther.compiler.query;

import souther.compiler.source.SourceId;

import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A problem that no longer exists is not still reported.
 *
 * <p>Recomputing an answer replaces what it said. A question that stops being asked at all is the
 * other case: nothing recomputes it, so whatever it last said would sit there unless the reports
 * are read from what the current answers are, rather than from every answer ever given.
 *
 * <p>An {@code examples for} file whose rows are all deleted is how that happens. The file is still
 * open, so its document still takes diagnostics; it just contributes no rows, so the question "do
 * this file's rows hold" is not asked any more.
 */
class StaleReportTest {

    private static final String CART = """
            module shop.cart exposing ( Total, double )

            data Total = Int

            behavior double : (n: Total) -> Total
                constructs Total
            let double (n) = Total(n.value * 2)
            """;

    private static final String FAILING_ROWS = """
            examples for shop.cart
            example double
              | "wrong" : (Total(2)) -> Total(5)
            """;

    /** The same file with its rows gone: still an `examples for` file, contributing nothing. */
    private static final String NO_ROWS = """
            examples for shop.cart
            """;

    private static Map<String, String> workspace(String rows) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("cart.sou", CART);
        byId.put("cart-examples.sou", rows);
        return byId;
    }

    @Test
    void anExampleFailureGoesAwayWhenItsRowIsDeleted() {
        Compilation c = Compilation.ofDocuments(workspace(FAILING_ROWS), Set.of(), ModulePath.EMPTY);
        Map<SourceId, List<souther.compiler.diag.Diagnostic>> first = Located.diagnosticsOf(c.diagnostics());
        assertEquals(1, first.get(new SourceId("cart-examples.sou")).size(),
                "the failing row is reported on the file it is written in");

        c.update(workspace(NO_ROWS), Set.of());

        assertEquals(List.of(), Located.diagnosticsOf(c.diagnostics()).get(new SourceId("cart-examples.sou")),
                "the row is gone, so its failure is gone");
    }

    @Test
    void aWholeCompilationStaysCleanAfterTheProblemIsRemoved() {
        Compilation c = Compilation.ofDocuments(workspace(FAILING_ROWS), Set.of(), ModulePath.EMPTY);
        Located.diagnosticsOf(c.diagnostics());
        c.update(workspace(NO_ROWS), Set.of());
        Located.diagnosticsOf(c.diagnostics());

        assertFalse(c.db().allReports().stream().anyMatch(f -> f.report().isError()),
                "nothing is wrong with this workspace any more");
    }
}
