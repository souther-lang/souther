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

    /**
     * A behavior is called by the name an import brought in, and not through the module.
     *
     * <p>{@code api.submit(d, s)} is {@code E1023} whether the name was imported or not and whether
     * the module was given an alias or not, so there is no qualified call for this to be asked
     * about. Written down here rather than left out: what a call's callee can be is what decides how
     * far into the source this reads, and the day a qualified one resolves is the day that has to be
     * looked at again.
     */
    @Test
    void aBehaviorIsCalledByTheNameThatWasBroughtIn() {
        assertEquals("submit(request: Draft, submittedAt: Stamp)",
                imported("submit(\n").orElseThrow().label());
        assertTrue(imported("api.submit(\n").isEmpty(),
                "a behavior is not reached through its module, so nothing is called here");
    }

    /** And a call written inside another that is also unclosed. */
    @Test
    void aCallInsideAnotherThatIsAlsoUnfinished() {
        SignatureHelp help = helpFor(model("submit(run(\n")).orElseThrow();

        assertEquals("run(d: Draft, s: Stamp)", help.label(),
                "the innermost is the one being written, and two brackets are missing");
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

    /** The same behavior, declared in another module and brought in by name. */
    private static Optional<SignatureHelp> imported(String body) {
        Map<String, String> sources = new LinkedHashMap<>();
        sources.put("file:///api.sou", """
                module api exposing ( Draft, Stamp, submit )

                data Draft = { plannedCost: Int }
                data Stamp = { at: Int }

                behavior submit : (request: Draft, submittedAt: Stamp) -> Int
                let submit (request, submittedAt) = request.plannedCost
                """);
        return helpIn(sources, """
                module m

                import api ( Draft, Stamp, submit )

                behavior run : (d: Draft, s: Stamp) -> Int
                let run (d, s) = \
                """ + body);
    }

    /** The cursor at the end of the last written line, which is where an author's is. */
    private static Optional<SignatureHelp> helpFor(String text) {
        return helpIn(new LinkedHashMap<>(), text);
    }

    private static Optional<SignatureHelp> helpIn(Map<String, String> beside, String text) {
        Map<String, String> sources = new LinkedHashMap<>(beside);
        sources.put(URI, text);
        ModuleGraph graph = ModuleGraph.of(sources);
        Analyzer analyzer = new Analyzer();
        analyzer.diagnostics(graph);

        List<String> lines = text.lines().toList();
        int on = lines.size() - 1;
        return analyzer.signatureHelp(URI, new Position(on, lines.get(on).length()), graph);
    }
}
