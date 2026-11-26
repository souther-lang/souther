package souther.compiler;

import souther.compiler.diag.HumanRenderer;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowIdentity;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Output;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a {@code _} row and a {@code with} answer is held to what the behavior they stand in for
 * declares, for the arguments the stand-in is called with, whoever implements that behavior.
 *
 * <p>Neither states an input, so neither can be held where it is written. A behavior with a body
 * holds its own answer in the body, and a stand-in takes the body's place, so the stand-in holds it
 * instead. A behavior another module declares is checked by nothing the calling code emits, so the
 * stand-in holds that one too, to the declaring module's clause.
 *
 * <p>Each refusal is read for the clause that stopped the row, since a row stopping for some other
 * reason would be refused with the same code.
 */
class AStandInIsHeldToWhatTheBehaviorItStandsInForDeclaresTest {

    /** A behavior implemented here, taking two inputs, that declares what it answers. */
    private static final String KEPT = """
            module probe.kept exposing ( top )

            behavior lookup : (key: Int) -> Int

            behavior convert : (a: Int, b: Int) -> Int
                depends on lookup
                ensures bounded = value < a + 100
            let convert (a, b, lookup) = lookup(a) + b

            behavior top : (a: Int, b: Int) -> Int
                depends on convert
            let top (a, b, convert) = convert(a, b)
            """;

    @Test
    void aDefaultRowTheDeclarationRulesOutStopsTheRowWhereItIsCalled() {
        Compilation c = refused(KEPT + """

                fake convert
                    | _ -> 500

                example top
                    | "past the bound" : (1, 2) -> 500
                """);

        stoppedBy(c, "past the bound", "probe.kept.convert: bounded");
    }

    @Test
    void aWithTheDeclarationRulesOutStopsTheRowWhereItIsCalled() {
        Compilation c = refused(KEPT + """

                example top
                    | "past the bound" : (1, 2) with convert = 500 -> 500
                """);

        stoppedBy(c, "past the bound", "probe.kept.convert: bounded");
    }

    /** The control for both: the same stand-ins answering what the declaration admits. */
    @Test
    void aStandInTheDeclarationAdmitsIsHeld() {
        held(compiles(KEPT + """

                fake convert
                    | _ -> 50

                example top
                    | "by the table" : (1, 2) -> 50
                    | "by the row" : (2, 1) with convert = 60 -> 60
                """), "by the table", "by the row");
    }

    /**
     * Held to the arguments the call was made with, and not to the row's. {@code top} calls
     * {@code convert} with {@code a + 200}: the answer is past the bound for the row's {@code a} and
     * within it for the one {@code convert} was given.
     */
    @Test
    void whatIsHeldIsTheCallTheStandInAnswered() {
        held(compiles(KEPT.replace("let top (a, b, convert) = convert(a, b)",
                "let top (a, b, convert) = convert(a + 200, b)") + """

                example top
                    | "within the bound of the call" : (1, 2) with convert = 250 -> 250
                """), "within the bound of the call");
    }

    /**
     * An answer reaching the union through a bridge case is held as the value it is. The clause is
     * written for the {@code Int} arm, and the check finds the arm by the case the value is; handed
     * the bridge case holding it, the check would find no arm and hold nothing.
     */
    @Test
    void anAnswerReachingTheUnionThroughABridgeIsHeldAsTheValueItIs() {
        Compilation c = refused("""
                module probe.bridged exposing ( top )

                data Missing = { key: Int }

                behavior lookup : (key: Int) -> Int

                behavior convert : (a: Int, b: Int) -> Int | Missing
                    depends on lookup
                    constructs Missing
                    ensures bounded = Int -> value < a + 100
                let convert (a, b, lookup) = if lookup(a) > b then lookup(a) else Missing { key = a }

                behavior top : (a: Int, b: Int) -> Int
                    depends on convert
                let top (a, b, convert) = match convert(a, b) with
                    | Int as n -> n
                    | Missing as m -> m.key + 200

                example top
                    | "past the bound" : (1, 2) with convert = 500 -> 500
                """);

        stoppedBy(c, "past the bound", "probe.bridged.convert: bounded");
    }

    /**
     * A behavior another module declares, stood in for here. The calling code emits no check for a
     * behavior it did not declare, so the stand-in holds it, to the clause the declaring module
     * wrote.
     */
    @Test
    void aStandInForABehaviorAnotherModuleDeclaresIsHeldToThatModulesClause() {
        Compilation c = ACompiledModel.refusedWith(List.of("E1905"), Compilation.ofSources(List.of("""
                module probe.rates exposing ( convert )

                behavior lookup : (key: Int) -> Int

                behavior convert : (a: Int, b: Int) -> Int
                    depends on lookup
                    ensures bounded = value < a + 100
                let convert (a, b, lookup) = lookup(a) + b
                """, """
                module probe.converting
                import probe.rates ( convert )

                behavior top : (a: Int, b: Int) -> Int
                    depends on convert
                let top (a, b, convert) = convert(a, b)

                example top
                    | "past the bound" : (1, 2) with convert = 500 -> 500
                """), ModulePath.EMPTY));

        stoppedBy(c, "past the bound", "probe.rates.convert: bounded");
    }

    // --- harness --------------------------------------------------------------------------------

    private static Compilation refused(String source) {
        return ACompiledModel.refusedWith(List.of("E1905"),
                Compilation.ofSources(List.of(source), ModulePath.EMPTY));
    }

    private static Compilation compiles(String source) {
        return ACompiledModel.compiles(Compilation.ofSources(List.of(source), ModulePath.EMPTY));
    }

    /** That the row {@code name} stopped while it ran, and what stopped it was {@code clause}. */
    private static void stoppedBy(Compilation c, String name, String clause) {
        RowOutcome row = rowNamed(c, name);
        assertEquals(List.of(Stage.INVOKED, Disposition.FAILED, FailurePhase.INVOCATION),
                List.of(row.stage(), row.disposition(), row.failurePhase()), row.toString());
        List<String> said = new ArrayList<>();
        c.diagnostics().values().stream().flatMap(List::stream).forEach(d -> said.add(
                new HumanRenderer(false).render(d.diagnostic(), null, Locale.ENGLISH)));
        assertTrue(said.stream().anyMatch(s -> s.contains("ensures not held on " + clause)),
                "the row was stopped by the clause of what was stood in for: " + said);
    }

    /** That the rows are {@code names}, and every one of them was compared and held. */
    private static void held(Compilation c, String... names) {
        List<String> found = new ArrayList<>();
        for (RowOutcome row : rows(c)) {
            found.add(row.identity().shown());
            assertEquals(List.of(Stage.COMPARED, Disposition.HELD, FailurePhase.NONE),
                    List.of(row.stage(), row.disposition(), row.failurePhase()), row.toString());
        }
        assertEquals(List.of(names), found, "the rows the model writes");
    }

    private static RowOutcome rowNamed(Compilation c, String name) {
        return rows(c).stream()
                .filter(row -> row.identity() instanceof RowIdentity.Named(String n) && n.equals(name))
                .findFirst().orElseThrow(() -> new AssertionError("no row `" + name + "`"));
    }

    /** Every row the module whose examples these are writes. */
    private static List<RowOutcome> rows(Compilation c) {
        Db db = c.db();
        List<RowOutcome> rows = new ArrayList<>();
        for (String module : c.modules()) {
            for (SourceId id : c.exampleSourcesOf(module)) {
                Output.Examples.Of ran = db.ask(new Output.Examples(module, id)).value();
                if (ran != null) {
                    rows.addAll(ran.rows());
                }
            }
        }
        return rows;
    }
}
