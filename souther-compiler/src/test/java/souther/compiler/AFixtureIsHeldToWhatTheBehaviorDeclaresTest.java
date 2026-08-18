package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code example} row and a {@code fake} table state values a behavior is given and answers with,
 * and an {@code ensures} states what has to hold between the two. Where a row states values that do
 * not, the row is refused.
 *
 * <p>The check is the emitted one. A row's operands are compiled and run as the module's own code, so
 * the values a row states exist in the loader as live values, and holding them to the declaration is
 * calling the same {@code $Ensures.check} that runs where the behavior answers. Nothing here reads a
 * clause and decides what it means a second time.
 *
 * <p>Which is why a row nothing runs yet is held too: the values are there whether or not anything
 * applies the behavior, and a recorded row that states an answer the model rules out is a wrong
 * record however long it waits for a body.
 */
class AFixtureIsHeldToWhatTheBehaviorDeclaresTest {

    private static final String DECLARED = """
            module example.todo

            data Id = Int
            data Todo = { id: Id, title: String }
            data NotFound

            behavior findTodo : (id: Id) -> Todo | NotFound
                ensures asked = Todo -> value.id.value == id.value
            """;

    /** The same model with nothing declared about the answer — the control every row here is read
     *  against, since a row that is refused where no clause is written was refused by something else. */
    private static final String UNDECLARED =
            DECLARED.replace("    ensures asked = Todo -> value.id.value == id.value\n", "");

    private static final String KEEPS_IT = """

            example findTodo
                | "the answer is the one asked for" : (Id(1)) -> Todo { id = Id(1), title = "write it" }
            """;

    private static final String BREAKS_IT = """

            example findTodo
                | "another id" : (Id(1)) -> Todo { id = Id(2), title = "write it" }
            """;

    // --- an example row -------------------------------------------------------------------------

    @Test
    void aRowStatingValuesTheClauseRelatesIsKept() {
        assertDoesNotThrow(() -> Compiler.compile(DECLARED + KEEPS_IT));
    }

    @Test
    void aRowStatingValuesTheClauseDoesNotRelateIsRefused() {
        CompileException refused = err(DECLARED + BREAKS_IT);

        assertTrue(codesOf(refused).contains("E1928"),
                "the row states an answer the declaration rules out: " + codesOf(refused));
        String said = rendered(only("E1928", refused));
        assertTrue(said.contains("findTodo"), "the behavior whose declaration it does not keep: " + said);
        assertTrue(said.contains("asked"), "and the clause that was not kept: " + said);
    }

    /** The control: the row is the same one, and with nothing declared there is nothing it fails. */
    @Test
    void theSameRowIsKeptWhereNothingIsDeclared() {
        assertDoesNotThrow(() -> Compiler.compile(UNDECLARED + BREAKS_IT));
    }

    @Test
    void whereTheRowStopsIsSaidOfTheRow() {
        List<RowOutcome> rows = rows(DECLARED + BREAKS_IT);

        assertEquals(1, rows.size());
        RowOutcome row = rows.get(0);
        assertEquals(Disposition.FAILED, row.disposition());
        assertEquals(FailurePhase.ENSURES, row.failurePhase());
        assertEquals(Stage.FIXTURES_VALIDATED, row.stage(),
                "the values were built and held to the declaration; nothing applied the behavior");
    }

    /**
     * A row with no body to run it is held all the same. Its values are what a migration harvested,
     * and a record of an answer the model rules out is wrong the day it is written.
     */
    @Test
    void aRowNothingRunsYetIsHeldToTheDeclaration() {
        CompileException refused = err(DECLARED + BREAKS_IT);

        assertTrue(codesOf(refused).contains("E1928"), codesOf(refused).toString());
        assertFalse(DECLARED.contains("let findTodo"), "nothing here applies the behavior");
    }

    /**
     * A bare case name states the arm and no value under it, so there is nothing to hand the check.
     * The clause below is one the row's input does not keep — {@code Id(0)} is not {@code > 0} — and
     * the row is kept, which is what says the check was not reached rather than reached and passed.
     */
    @Test
    void aRowStatingOnlyACaseIsNotHeldToTheClause() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound

                behavior findTodo : (id: Id) -> Todo | NotFound
                    ensures positive = NotFound -> id.value > 0

                example findTodo
                    | "nothing is found for zero" : (Id(0)) -> NotFound
                """));
    }

    /**
     * An answer carried by a primitive. What a row built is handed to the check as the boxed carrier
     * it is, which is what the check's all-reference ABI is for: the row's value never took the form
     * the behavior's body runs on, and nothing here converts it to one.
     */
    @Test
    void anAnswerCarriedByAPrimitiveIsHeldAsTheCarrierItIs() {
        String model = """
                module example.amount

                data Amount = Int

                behavior twice : (a: Amount) -> Amount
                    constructs Amount
                    ensures doubled = value.value == a.value * 2

                let twice (a) = Amount { value = a.value * 2 }

                example twice
                """;

        assertDoesNotThrow(() -> Compiler.compile(model
                + "    | \"three doubles to six\" : (Amount(3)) -> Amount(6)\n"));

        CompileException refused = err(model
                + "    | \"three doubles to seven\" : (Amount(3)) -> Amount(7)\n");
        assertTrue(codesOf(refused).contains("E1928"), codesOf(refused).toString());
    }

    // --- a fake's table -------------------------------------------------------------------------

    private static final String DEPENDS = """
            module example.order

            data Id = Int
            data Found = { id: Id }
            data Missing
            data Placed = { by: Id }

            behavior lookup : (id: Id) -> Found | Missing
                ensures asked = Found -> value.id.value == id.value

            behavior place : (id: Id) -> Placed
                depends on lookup
                constructs Placed

            let place (id, lookup) = match lookup(id) with
                | Found   -> Placed { by = id }
                | Missing -> Placed { by = id }
            """;

    @Test
    void aFakeRowStatingValuesTheClauseDoesNotRelateIsRefused() {
        CompileException refused = err(DEPENDS + """

                fake lookup
                    | (Id(1)) -> Found { id = Id(2) }
                """);

        assertTrue(codesOf(refused).contains("E1929"),
                "the table stands in with an answer the declaration rules out: " + codesOf(refused));
        String said = rendered(only("E1929", refused));
        assertTrue(said.contains("lookup"), "the dependency whose declaration it does not keep: " + said);
    }

    @Test
    void aFakeRowStatingValuesTheClauseRelatesIsKept() {
        assertDoesNotThrow(() -> Compiler.compile(DEPENDS + """

                fake lookup
                    | (Id(1)) -> Found { id = Id(1) }
                """));
    }

    /** A `_` row states no input, so there is nothing to hold its output against here. */
    @Test
    void aDefaultFakeRowIsNotHeldHere() {
        assertDoesNotThrow(() -> Compiler.compile(DEPENDS + """

                fake lookup
                    | _ -> Found { id = Id(7) }
                """));
    }

    /**
     * What it answers is held where it answers. A `_` stands in as an injected dependency, so the
     * generated code that calls it goes through the crossing check — and a row that reaches it is
     * told the clause was not kept, as the row's own abort rather than as a statement about the
     * table.
     */
    @Test
    void whatADefaultFakeAnswersIsHeldAtTheCrossing() {
        CompileException refused = err(DEPENDS + """

                fake lookup
                    | _ -> Found { id = Id(7) }

                example place
                    | "it is placed for the one asked" : (Id(1)) -> Placed { by = Id(1) }
                """);

        assertFalse(codesOf(refused).contains("E1929"),
                "the table states no input here, so nothing was held against it: "
                        + codesOf(refused));
        String said = rendered(refused.diagnostics().get(0));
        assertTrue(said.contains("aborted") && said.contains("ensures not held")
                        && said.contains("lookup"),
                "the row was stopped by the dependency's own check: " + said);
    }

    // --- harness --------------------------------------------------------------------------------

    private static CompileException err(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model));
    }

    private static List<String> codesOf(CompileException e) {
        List<String> codes = new ArrayList<>();
        for (Diagnostic d : e.diagnostics()) {
            codes.add(d.code());
        }
        return codes;
    }

    private static Diagnostic only(String code, CompileException e) {
        for (Diagnostic d : e.diagnostics()) {
            if (code.equals(d.code())) {
                return d;
            }
        }
        throw new AssertionError("no " + code + " among " + codesOf(e));
    }

    private static String rendered(Diagnostic d) {
        return new HumanRenderer(false).render(d, null, Locale.ENGLISH);
    }

    private static List<RowOutcome> rows(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        return compilation.db()
                .ask(Output.Examples.asked(compilation.db(), compilation.modules().get(0),
                        compilation.sourceIds().get(0)))
                .value().rows();
    }
}
