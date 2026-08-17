package souther.lsp.analysis;

import souther.lsp.protocol.CompletionItem;
import souther.lsp.protocol.Position;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value an attached file declares is offered where it may be written.
 *
 * <p>Those values join the module the rows join, so they reach both of a module's files under the
 * same names — and only the rows may write one (spec §an-attached-files-values-are-for-its-rows).
 * Offered in the model source, the editor would be suggesting a name the compiler refuses, which is
 * a worse answer than not suggesting it: an author can always type a name that was not offered.
 *
 * <p>Answered per document, which is the grain this list has. It is not context-sensitive at all, so
 * an inline {@code example} row in the model source may write such a value and is not offered it.
 */
class WhatIsOfferedIsWhatMayBeWrittenInThisDocumentTest {

    private static final String MODEL_URI = "file:///m.sou";
    private static final String ATTACHED_URI = "file:///m.examples.sou";

    private static final String MODEL = """
            module m exposing ( Amount, echo )

            data Amount = { n: Int }

            behavior echo : (x: Amount) -> Amount
            let echo (x) = x
            """;

    private static final String ATTACHED = """
            examples for m

            let floor = Amount { n = 0 }

            example echo
                | "unchanged" : (floor) -> floor
            """;

    private static ModuleGraph graph() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(MODEL_URI, MODEL);
        sources.put(ATTACHED_URI, ATTACHED);
        return ModuleGraph.of(sources);
    }

    private static List<String> labels(List<CompletionItem> items) {
        List<String> out = new ArrayList<>();
        for (CompletionItem item : items) {
            out.add(item.label());
        }
        return out;
    }

    /** The cursor in the body of `let echo (x) = x`, the last line of {@link #MODEL}. */
    private static final Position IN_THE_MODELS_BODY = new Position(5, 15);

    /** The cursor on the blank line under the attached file's `let`. */
    private static final Position BESIDE_THE_ROWS = new Position(3, 0);

    @Test
    void theModelSourceIsNotOfferedOne() {
        List<String> offered =
                labels(new Analyzer().completions(MODEL_URI, IN_THE_MODELS_BODY, graph()));

        assertFalse(offered.contains("floor"),
                "`floor` is the rows', and writing it here is refused: " + offered);
        assertTrue(offered.contains("Amount"),
                "what the model does reach is offered as before: " + offered);
    }

    @Test
    void theAttachedFileIsOfferedOne() {
        List<String> offered =
                labels(new Analyzer().completions(ATTACHED_URI, BESIDE_THE_ROWS, graph()));

        assertTrue(offered.contains("Amount"),
                "the model's declarations are from elsewhere here, and are offered: " + offered);
    }

    /**
     * A module's own value is offered in its own source, whatever else the workspace holds.
     *
     * <p>The rule is about which declaration a name reaches and not about a module having an
     * attached file: a `let` the model wrote is the model's, and one written beside it is not.
     */
    @Test
    void aValueTheModelDeclaresIsStillOffered() {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(MODEL_URI, """
                module m exposing ( Amount, echo )

                data Amount = { n: Int }

                let base = 0

                behavior echo : (x: Amount) -> Amount
                let echo (x) = x
                """);
        sources.put(ATTACHED_URI, """
                examples for m

                let floor = Amount { n = base }

                example echo
                    | "unchanged" : (floor) -> floor
                """);
        List<String> offered = labels(new Analyzer()
                .completions(ATTACHED_URI, BESIDE_THE_ROWS, ModuleGraph.of(sources)));

        assertTrue(offered.contains("base"),
                "the model's own value reaches the rows and is offered to them: " + offered);
    }
}
