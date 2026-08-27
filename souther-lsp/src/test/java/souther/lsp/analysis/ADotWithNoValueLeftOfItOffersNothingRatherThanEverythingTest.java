package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.Position;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The two places a {@code .} is written that this reading has no member list for. Both offer
 * nothing, and that is the answer rather than a gap: what may be written after a {@code .} is not
 * every name in scope, and offering the name list there would be answering a question nobody asked.
 */
class ADotWithNoValueLeftOfItOffersNothingRatherThanEverythingTest {

    private static final String URI = "file:///m.sou";

    /**
     * A bare {@code .field} is the getter {@code (x) -> x.field} and has no receiver at all.
     *
     * <p>What it could be answered from is the type the position it stands in expects, which is a
     * different question from what a value is — an expected type is not what an expression is — and
     * nothing here reads one.
     */
    @Test
    void aGetterWrittenWithNoReceiverIsOfferedNothing() {
        assertEquals(List.of(), offeredAfterTheDot("""
                module m

                data Draft = { plannedCost: Int }

                behavior each : (ds: List<Draft>) -> List<Int>
                let each (ds) = List.map(ds, .
                """));
    }

    /**
     * And a type's own name to the left of one.
     *
     * <p>{@code MemberId.decoder} reaches what a declaration writes for itself rather than a field
     * of a value, and this reading does not answer about those. It is not a namespace either — a
     * qualifier names a module or one of the language's own, and a type name is neither — so what is
     * left is a receiver whose type no declaration read here states.
     */
    @Test
    void aTypeNameToTheLeftOfADotIsOfferedNothing() {
        assertEquals(List.of(), offeredAfterTheDot("""
                module m

                data MemberId = { value: Text }

                behavior f : (m: MemberId) -> Text
                let f (m) = MemberId.
                """));
    }

    private static List<String> offeredAfterTheDot(String text) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, text);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);

        List<String> lines = text.lines().toList();
        int on = lines.size() - 1;
        List<String> labels = new ArrayList<>();
        for (CompletionItem item
                : analyzer.completions(URI, new Position(on, lines.get(on).length()), graph)) {
            labels.add(item.label());
        }
        return labels;
    }
}
