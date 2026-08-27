package souther.lsp.analysis;

import org.junit.jupiter.api.Test;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.SignatureHelp;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A signature is wanted while the call is half written — {@code submit(} has no closing bracket and
 * does not parse. The declaration is read at the callee's name, which is written before any of that;
 * which argument is being written is counted in the source the author left, so a bracket supplied to
 * make the line parse is not one of the commas.
 */
class WhichArgumentIsBeingWrittenIsCountedInWhatTheAuthorLeftTest {

    private static final String URI = "file:///m.sou";

    private static String model(String body) {
        return """
                module m

                data Draft = { plannedCost: Int }
                data Stamp = { at: Int }

                behavior submit : (request: Draft, submittedAt: Stamp) -> Int
                let submit (request, submittedAt) = request.plannedCost

                behavior run : (d: Draft, s: Stamp) -> Int
                let run (d, s) = \
                """ + body;
    }

    @Test
    void theDeclarationIsShownWhileTheCallIsUnclosed() {
        SignatureHelp help = helpFor(model("submit(\n")).orElseThrow();

        assertEquals("submit(request: Draft, submittedAt: Stamp)", help.label());
        assertEquals(List.of("request: Draft", "submittedAt: Stamp"), help.parameters());
        assertEquals(0, help.active(), "nothing is written yet, so it is the first");
    }

    @Test
    void aCommaMovesToTheNextParameter() {
        assertEquals(1, helpFor(model("submit(d,\n")).orElseThrow().active());
    }

    /**
     * And a comma inside something else does not.
     *
     * <p>A comma in a nested call, a tuple or a construction belongs to that, and counting it would
     * move a reader along a signature they are not in.
     */
    @Test
    void aCommaInsideSomethingElseIsNotOneOfThese() {
        assertEquals(0, helpFor(model("submit(run(d, s)\n")).orElseThrow().active(),
                "the comma is `run`'s, and the cursor is still writing `submit`'s first argument");
    }

    @Test
    void aCursorInNoCallIsToldNothing() {
        assertTrue(helpFor(model("request.plannedCost\n")).isEmpty());
    }

    @Test
    void aCalleeThatIsNoBehaviorIsToldNothing() {
        // A local holding nothing declared on a `behavior` line.
        assertTrue(helpFor(model("d(\n")).isEmpty(),
                "what a local takes is not written on a `behavior` line");
    }

    /** The cursor at the end of the last written line, which is where an author's is. */
    private static Optional<SignatureHelp> helpFor(String text) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put(URI, text);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);

        List<String> lines = text.lines().toList();
        int on = lines.size() - 1;
        return analyzer.signatureHelp(URI, new Position(on, lines.get(on).length()), graph);
    }
}
