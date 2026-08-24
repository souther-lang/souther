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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
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

    private static final String EDGES = "file:///edges.sou";

    /** A behavior whose only gaps are the two lines its invariant draws: the output is one data, the
     *  body forks nowhere, and the one row covers the one class the position divides into. So the
     *  block a person is offered holds boundary rows or nothing. */
    private static final String ONLY_EDGES = """
            module edges

            data Amount = Int
                invariant value >= 0 && value <= 10

            data Ok = { n: Amount }

            behavior keep : (a: Amount) -> Ok
                constructs Ok

            let keep (a) = Ok { n = a }

            example keep
                | "mid" : (Amount(5)) -> Ok { n = Amount(5) }
            """;

    private static ModuleGraph graphOf(Map<String, String> documents) {
        return ModuleGraph.of(new LinkedHashMap<>(documents));
    }

    private static Analyzer measuring(Adequacy.Level level) {
        return measuring(level, true);
    }

    /** @param resolves what the client's handshake said about coming back for an action's edit */
    private static Analyzer measuring(Adequacy.Level level, boolean resolves) {
        Analyzer analyzer = new Analyzer();
        analyzer.measure(Adequacy.Asked.reportOnly(level));
        analyzer.resolvesActions(resolves);
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
        assertEquals("1 row · out 1/2 · boundary 2/6 · branch 1/2", lenses.get(0).title());
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
        assertEquals("2 rows · out 2/2 · boundary 3/6 · branch 2/2", lenses.get(0).title());
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
        Analyzer analyzer = measuring(Adequacy.Level.ALL);
        ModuleGraph graph = graphOf(Map.of(MODULE, TRIP));
        List<CodeAction> actions = analyzer.codeActions(MODULE, TRIP, on(9), graph);

        assertEquals(1, actions.size(), actions.toString());
        assertEquals("Write the rows `submit` does not cover", actions.get(0).title());
        // Offered without the rows, which is the point of offering it: what they cost is paid by
        // somebody taking it.
        CodeAction.Deferred offered =
                assertInstanceOf(CodeAction.Deferred.class, actions.get(0));

        CodeAction.Applied taken = analyzer.resolve(offered, TRIP, graph);
        assertNotNull(taken, "and taking it writes rows");
        for (String line : taken.newText().lines().filter(l -> !l.isBlank()).toList()) {
            assertTrue(line.startsWith("//"), "every line is a comment: " + line);
        }
        assertTrue(taken.newText().contains("-> <?>"), taken.newText());
    }

    /**
     * A client that will not come back for the edit is handed it.
     *
     * <p>What the handshake settles is when the rows are worked out, and never whether the offer is
     * made. Deferring to a client that does not resolve would show an offer that does nothing when
     * it is taken, which is the same source-with-no-rows the eager path was written against.
     */
    @Test
    void aClientThatDoesNotResolveIsHandedTheEditWithTheOffer() {
        ModuleGraph graph = graphOf(Map.of(MODULE, TRIP));
        List<CodeAction> actions = measuring(Adequacy.Level.ALL, false)
                .codeActions(MODULE, TRIP, on(9), graph);

        assertEquals(1, actions.size(), actions.toString());
        CodeAction.Applied eager = assertInstanceOf(CodeAction.Applied.class, actions.get(0));

        Analyzer resolving = measuring(Adequacy.Level.ALL, true);
        CodeAction.Deferred offered = assertInstanceOf(CodeAction.Deferred.class,
                resolving.codeActions(MODULE, TRIP, on(9), graph).get(0));
        assertEquals(eager.newText(), resolving.resolve(offered, TRIP, graph).newText(),
                "and the rows are the same rows either way");
    }

    /**
     * An offer names a behavior of a module written in a document, and taking it checks all three.
     *
     * <p>A document can be given another module's header while a behavior of that name goes on
     * existing somewhere else. Checked only against the module, the rows would be composed from the
     * source that still has the behavior and written into the one that no longer does.
     */
    @Test
    void anOfferIsNotTakenWhereItsBehaviorHasMovedToAnotherDocument() {
        String other = "file:///other.sou";
        Analyzer analyzer = measuring(Adequacy.Level.ALL);
        ModuleGraph before = graphOf(Map.of(MODULE, TRIP));
        CodeAction.Deferred offered = assertInstanceOf(CodeAction.Deferred.class,
                analyzer.codeActions(MODULE, TRIP, on(9), before).get(0));

        // The document the offer was made about now declares something else, and what it was made
        // about is written in the other one.
        ModuleGraph after = graphOf(Map.of(
                MODULE, TRIP.replaceFirst("module \\S+", "module example.moved"),
                other, TRIP));
        assertNull(analyzer.resolve(offered, TRIP, after),
                "the behavior the offer names is not written in the document it names");
    }

    /**
     * The rows at an edge are offered whatever the build was measuring.
     *
     * <p>What an author asked for by taking "write the rows this does not cover" is those rows.
     * Composing a value costs a decoder run for each point it settles, which is not what a build at
     * {@code witness} promises — so the measurement composes none, and a build is not slowed by
     * values nobody asked to see. But taking the action is asking, and it is asked once rather than
     * on every keystroke, so what it costs is paid where somebody wanted it.
     *
     * <p>The level does not decide it, because it is not about how much to measure. Read off the
     * level, the editor offered to write rows at {@code witness} and put a comment in somebody's
     * source, since the block held the reason nothing was composed and no rows.
     *
     * <p>An offer to write rows still has to write rows. What there is to write is the generator's
     * answer either way, and the block is asked how many rows it holds rather than whether its text
     * is blank.
     */
    @Test
    void theRowsAtAnEdgeAreOfferedWhateverTheBuildMeasured() {
        assertEquals(1, measuring(Adequacy.Level.ALL)
                        .codeActions(EDGES, ONLY_EDGES, on(7),
                                graphOf(Map.of(EDGES, ONLY_EDGES))).size(),
                "at `all` the two lines are rows to write");

        assertEquals(1, measuring(Adequacy.Level.WITNESS)
                        .codeActions(EDGES, ONLY_EDGES, on(7),
                                graphOf(Map.of(EDGES, ONLY_EDGES))).size(),
                "and at `witness` they are the same rows: taking the action is what asks for them");
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

    /**
     * A line whose value could not be read is left out of the ratio.
     *
     * <p>A lens is one number on one line and has nowhere to put a word beside it. The report writes
     * "undecided" next to the count and can afford to include such a line; drawn over a declaration
     * the same line reads as a row the author has not written, at a value nothing was able to look
     * at. So the ratio counts the lines that came to an answer, and the rest are absent rather than
     * counted as missing.
     *
     * <p>The row below hands the behavior more nodes than an observation keeps, so the value at
     * {@code cost} is truncated and the boundaries there are undecided.
     */
    @Test
    void aLineWhoseValueCouldNotBeReadIsNotInTheRatio() {
        // Computed rather than spelled: a row's operand is compiled as a method of the module, and
        // a literal this size is past what a JVM method holds — which would leave the module with
        // no classes at all, where what this measures is the observation's limit.
        String groups = "someGroups(64)";
        String unread = """
                module example.wide

                data Amount = Int
                    invariant value >= 0 && value <= 1000

                data Item = { a: String, b: String, c: String }
                data Group = { items: List<Item> }
                data Draft = { groups: List<Group>, cost: Amount }
                data Ok = { n: Int }

                behavior take : (request: Draft) -> Ok
                    constructs Ok

                let take (request) = Ok { n = request.cost.value }

                let someItems (n: Int): List<Item> =
                    List.map({ (i) -> Item { a = "x", b = "x", c = "x" } }, List.rangeInclusive(1, n))

                let someGroups (n: Int): List<Group> =
                    List.map({ (i) -> Group { items = someItems(64) } }, List.rangeInclusive(1, n))

                example take
                    | (Draft { groups = %s, cost = Amount(0) }) -> Ok { n = 0 }
                """.formatted(groups);

        List<CodeLens> lenses = measuring(Adequacy.Level.ALL)
                .codeLenses(MODULE, graphOf(Map.of(MODULE, unread)));

        assertEquals(1, lenses.size());
        assertFalse(lenses.get(0).title().contains("boundary"),
                "the invariant draws two lines and neither was decided: " + lenses.get(0).title());
    }
}
