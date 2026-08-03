package souther.lsp;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.lsp.analysis.Analyzer;
import souther.lsp.analysis.ModuleGraph;
import souther.lsp.protocol.CodeAction;
import souther.lsp.protocol.CodeLens;
import souther.lsp.protocol.Position;
import souther.lsp.protocol.Range;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an editor is told about the rows, where the author is working.
 *
 * <p>Off unless asked for, and answered from the workspace or not at all. One document cannot say
 * what a behavior's rows cover: they are written across its module's own source and any number of
 * attached files, so reading one file would report what another covers as uncovered — which is worse
 * than saying nothing, being wrong rather than absent.
 */
class AdequacyLensTest {

    private static final String MODULE = "file:///trip.sou";
    private static final String ATTACHED = "file:///trip.examples.sou";

    private static final String TRIP = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (request: Draft) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (request) = {
                guard request.cost.value <= 100 else Waiting { cost = request.cost }
                Submitted { cost = request.cost }
            }

            example submit
                | (Draft { cost = Amount(50) }) -> Submitted { cost = Amount(50) }
            """;

    private static ModuleGraph graphOf(Map<String, String> documents) {
        return ModuleGraph.of(new LinkedHashMap<>(documents));
    }

    private static Analyzer measuring(Adequacy.Level level) {
        Analyzer analyzer = new Analyzer();
        analyzer.measure(Adequacy.Asked.reportOnly(level));
        return analyzer;
    }

    /** The default. Nothing is measured, so nothing is drawn. */
    @Test
    void anEditorThatDidNotAskIsShownNothing() {
        Analyzer analyzer = new Analyzer();

        assertEquals(List.of(),
                analyzer.codeLenses(MODULE, graphOf(Map.of(MODULE, TRIP))));
        assertFalse(analyzer.measuring());
    }

    /** Asked for, the numbers appear on the behavior's own line. */
    @Test
    void theNumbersAreDrawnOnTheDeclarationTheyAreAbout() {
        List<CodeLens> lenses = measuring(Adequacy.Level.ALL)
                .codeLenses(MODULE, graphOf(Map.of(MODULE, TRIP)));

        assertEquals(1, lenses.size());
        assertEquals(9, lenses.get(0).range().start().line(), "the `behavior` line, zero-based");
        assertEquals("1 row · out 1/2 · boundary 0/3 · branch 1/2", lenses.get(0).title());
    }

    /**
     * A row in an attached file counts.
     *
     * <p>This is the reason the question is asked of a workspace. The second row is written in
     * another document entirely, and it is what makes `Waiting` a case something claims.
     */
    @Test
    void aRowInAnAttachedFileIsCounted() {
        Map<String, String> workspace = new LinkedHashMap<>();
        workspace.put(MODULE, TRIP);
        workspace.put(ATTACHED, """
                examples for example.trip

                example submit
                    | (Draft { cost = Amount(500) }) -> Waiting { cost = Amount(500) }
                """);

        List<CodeLens> lenses = measuring(Adequacy.Level.ALL).codeLenses(MODULE, graphOf(workspace));

        assertEquals(1, lenses.size());
        assertEquals("2 rows · out 2/2 · boundary 0/3 · branch 2/2", lenses.get(0).title());
    }

    /** Nothing has been claimed about a behavior no row names, so there is nothing to draw over it. */
    @Test
    void aBehaviorNoRowNamesGetsNoLine() {
        String unexampled = TRIP.substring(0, TRIP.indexOf("example submit"));

        assertEquals(List.of(), measuring(Adequacy.Level.ALL)
                .codeLenses(MODULE, graphOf(Map.of(MODULE, unexampled))));
    }

    /** Below `all` the arms are not run, so the branch figure is left off rather than printed as
     * nothing reached. */
    @Test
    void whatWasNotMeasuredIsLeftOffRatherThanShownAsZero() {
        String title = measuring(Adequacy.Level.WITNESS)
                .codeLenses(MODULE, graphOf(Map.of(MODULE, TRIP))).get(0).title();

        assertTrue(title.startsWith("1 row · out 1/2"), title);
        assertFalse(title.contains("branch"), title);
    }

    // --- writing the rows in ----------------------------------------------------------------------

    private static Range on(int line) {
        return new Range(new Position(line, 0), new Position(line, 0));
    }

    /**
     * The offer on a behavior's declaration writes the block `--generate` prints.
     *
     * <p>Commented out and with every answer left open, for the same reason the command's output is:
     * the compiler does not know what the model owes, and a row it filled in would be an assertion
     * nobody made.
     */
    @Test
    void theRowsABehaviorDoesNotCoverCanBeWrittenIn() {
        List<CodeAction> actions = measuring(Adequacy.Level.ALL)
                .codeActions(MODULE, TRIP, on(9), graphOf(Map.of(MODULE, TRIP)));

        assertEquals(1, actions.size(), actions.toString());
        assertEquals("Write the rows `submit` does not cover", actions.get(0).title());
        for (String line : actions.get(0).newText().lines().filter(l -> !l.isBlank()).toList()) {
            assertTrue(line.startsWith("//"), "every line is a comment: " + line);
        }
        assertTrue(actions.get(0).newText().contains("-> <?>"), actions.get(0).newText());
    }

    /** With one document there is nothing to offer: the values a row writes are built through the
     * module's derived decoders, and its imports are part of that. */
    @Test
    void withNoWorkspaceThereIsNothingToOffer() {
        assertEquals(List.of(),
                measuring(Adequacy.Level.ALL).codeActions(MODULE, TRIP, on(9)));
    }

    /** And nothing is offered where nothing was asked to be measured. */
    @Test
    void anEditorThatDidNotAskIsOfferedNothing() {
        assertEquals(List.of(), new Analyzer()
                .codeActions(MODULE, TRIP, on(9), graphOf(Map.of(MODULE, TRIP))));
    }
}
