package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.FailurePhase;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.meta.ModulePath;
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

    /** An answer whose case carries fields, and a clause an arm decides on its own. */
    private static final String CARRIES_FIELDS = """
            module example.todo

            data Id = Int
            data Todo = { id: Id, title: String }
            data NotFound = { asked: Id }

            behavior findTodo : (id: Id) -> Todo | NotFound
                ensures positive = NotFound -> id.value > 0

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
     * A bare case name that is a unit case is the whole answer. There is one value of that type, so
     * naming it writes the answer rather than standing for values the row did not write — and the
     * spec's reading of an arm as a reference to the answer is exactly that. The clause below is one
     * the row's input does not keep, and the row is refused although it wrote no construction.
     */
    @Test
    void aRowStatingOnlyAUnitCaseIsHeldToTheClause() {
        CompileException refused = err("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound

                behavior findTodo : (id: Id) -> Todo | NotFound
                    ensures positive = NotFound -> id.value > 0

                example findTodo
                    | "nothing is found for zero" : (Id(0)) -> NotFound
                """);

        assertTrue(codesOf(refused).contains("E1928"),
                "the arm names the answer, and the input is written: " + codesOf(refused));
    }

    /** The same row with an input the clause keeps. */
    @Test
    void aRowStatingOnlyAUnitCaseTheClauseAdmitsIsKept() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound

                behavior findTodo : (id: Id) -> Todo | NotFound
                    ensures positive = NotFound -> id.value > 0

                example findTodo
                    | "nothing is found for one" : (Id(1)) -> NotFound
                """));
    }

    /**
     * A bare case name that carries fields writes no value, and it does name the answer. What the
     * row gives is the case the answer is, and every rule that case decides on its own is run over
     * it — here a rule reading only the input, which the row's input does not keep.
     */
    @Test
    void aRowStatingOnlyACaseThatCarriesFieldsIsHeldToWhatItsArmDecides() {
        CompileException refused = err(CARRIES_FIELDS + """
                example findTodo
                    | "nothing is found for zero" : (Id(0)) -> NotFound
                """);

        assertTrue(codesOf(refused).contains("E1928"),
                "the arm names the answer, and the input is written: " + codesOf(refused));
        String said = rendered(only("E1928", refused));
        assertTrue(said.contains("positive"), "and the clause that was not kept: " + said);
    }

    /** The same row with an input the clause keeps. */
    @Test
    void aRowStatingOnlyACaseThatCarriesFieldsAndKeepsTheClauseIsKept() {
        assertDoesNotThrow(() -> Compiler.compile(CARRIES_FIELDS + """
                example findTodo
                    | "nothing is found for one" : (Id(1)) -> NotFound
                """));
    }

    /** The control: the same row, with nothing declared for it to fail. */
    @Test
    void theSameCaseOnlyRowIsKeptWhereNothingIsDeclared() {
        assertDoesNotThrow(() -> Compiler.compile(
                CARRIES_FIELDS.replace("    ensures positive = NotFound -> id.value > 0\n", "") + """
                example findTodo
                    | "nothing is found for zero" : (Id(0)) -> NotFound
                """));
    }

    /** Where such a row stops is where any row held to the declaration stops. */
    @Test
    void whereACaseOnlyRowStopsIsSaidOfTheRow() {
        List<RowOutcome> rows = rows(CARRIES_FIELDS + """
                example findTodo
                    | "nothing is found for zero" : (Id(0)) -> NotFound
                """);

        assertEquals(1, rows.size());
        assertEquals(Disposition.FAILED, rows.get(0).disposition());
        assertEquals(FailurePhase.ENSURES, rows.get(0).failurePhase());
        assertEquals(Stage.FIXTURES_VALIDATED, rows.get(0).stage());
    }

    /**
     * A rule that reads the answer is not decided from the case alone, which is the honest answer
     * for a row that wrote no value. Read against the row below it, which writes one and is refused
     * by the same clause — so what is silent here is the missing value and not a clause nothing
     * runs.
     */
    @Test
    void aRuleReadingTheAnswerIsNotDecidedFromTheCaseAlone() {
        String model = """
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound = { asked: Id }

                behavior findTodo : (id: Id) -> Todo | NotFound
                    ensures asked = NotFound -> value.asked.value == id.value

                example findTodo
                """;

        assertDoesNotThrow(() -> Compiler.compile(model
                + "    | \"the case alone\" : (Id(1)) -> NotFound\n"));

        CompileException refused = err(model
                + "    | \"a value that does not keep it\" : (Id(1)) -> NotFound { asked = Id(2) }\n");
        assertTrue(codesOf(refused).contains("E1928"), codesOf(refused).toString());
    }

    /**
     * An arm may name a sum, and a row names one of its leaves. Which rules a leaf is held to is
     * worked out where the check is emitted, so the arm `Errors` decides for the `NotFound` a row
     * writes.
     *
     * <p>Two case names meet here and the message carries the arm's: the row answered `NotFound`
     * and the rule that refused it is written for `Errors`. Pinned as it stands rather than left to
     * be read either way — what an `EnsuresFailure` names is the same on the path that has a value,
     * where a rule written for a sum refuses a leaf just as it does here, and which of the two it
     * should carry is a question about that record and not about this row (#830).
     */
    @Test
    void anArmNamingASumDecidesForEachLeafItHas() {
        CompileException refused = err("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound = { asked: Id }
                data Denied = { asked: Id }
                data Errors = NotFound | Denied

                behavior findTodo : (id: Id) -> Todo | Errors
                    ensures positive = Errors -> id.value > 0

                example findTodo
                    | "nothing is found for zero" : (Id(0)) -> NotFound
                """);

        assertTrue(codesOf(refused).contains("E1928"),
                "`NotFound` is a leaf of the arm `Errors`: " + codesOf(refused));
        assertTrue(rendered(only("E1928", refused)).contains("answering Errors"),
                "the arm the refusing rule is written for, not the leaf the row wrote: "
                        + rendered(only("E1928", refused)));
    }

    /** And a leaf the arm does not name is held to nothing the arm states. */
    @Test
    void aRuleIsNotAppliedToACaseItsArmDoesNotName() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound = { asked: Id }
                data Denied = { asked: Id }

                behavior findTodo : (id: Id) -> Todo | NotFound | Denied
                    ensures positive = NotFound -> id.value > 0

                example findTodo
                    | "denied for zero" : (Id(0)) -> Denied
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

    /**
     * A table with such a row is not one to stand in with, as a table that will not build is not. A
     * row reaching it stops without a fake and says nothing of its own — what is wrong is wrong
     * about the table, and is said once where the table is written.
     *
     * <p>Not left to the check the stand-in's answer would meet at the crossing. That would run the
     * rest of the behavior with a dependency in a state the model rules out, and everything the row
     * then reported would be about a run that cannot happen.
     */
    @Test
    void aRowReachingSuchATableDoesNotRunAgainstIt() {
        List<RowOutcome> rows = rows(DEPENDS + """

                fake lookup
                    | (Id(1)) -> Found { id = Id(2) }

                example place
                    | "it is placed for the one asked" : (Id(1)) -> Placed { by = Id(1) }
                """);

        assertEquals(1, rows.size());
        assertEquals(Disposition.FAILED, rows.get(0).disposition());
        assertEquals(FailurePhase.FAKE_RESOLUTION, rows.get(0).failurePhase(),
                "the row had no table it could stand in with");
    }

    @Test
    void aFakeRowStatingValuesTheClauseRelatesIsKept() {
        assertDoesNotThrow(() -> Compiler.compile(DEPENDS + """

                fake lookup
                    | (Id(1)) -> Found { id = Id(1) }
                """));
    }

    /**
     * A fake stands in with a value, and a bare case name carrying fields is not one. Such a name
     * denotes a value only where the type has one — a unit case — so in a fake's answer it is
     * <em>E1023</em> before anything holds it, and the case-alone reading an {@code example} row's
     * expectation gets is not one this position has.
     *
     * <p>Written down because it is what keeps the two apart. A row's expectation may name the case
     * the answer is, because reporting a disagreement about the case is what a row is for; a fake
     * answers a dependency, and a value is what the behavior it stands in for is given.
     */
    @Test
    void aFakeAnsweringWithACaseThatCarriesFieldsNamesNoValue() {
        List<String> codes = codesOf(Compilation.ofSource("""
                module example.order

                data Id = Int
                data Found = { id: Id }
                data Missing = { asked: Id }

                behavior lookup : (id: Id) -> Found | Missing
                    ensures positive = Missing -> id.value > 0

                data Placed = { by: Id }

                behavior place : (id: Id) -> Placed
                    depends on lookup
                    constructs Placed

                let place (id, lookup) = match lookup(id) with
                    | Found   -> Placed { by = id }
                    | Missing -> Placed { by = id }

                fake lookup
                    | (Id(0)) -> Missing
                """, "Main"));

        assertTrue(codes.contains("E1023"),
                "`Missing` carries fields, so it names no value here: " + codes);
        assertFalse(codes.contains("E1929"),
                "nothing was built for the declaration to be asked about: " + codes);
    }

    /** The same table with the value written, which the declaration then rules out. */
    @Test
    void aFakeAnsweringWithSuchACaseWrittenOutIsHeld() {
        List<String> codes = codesOf(Compilation.ofSource("""
                module example.order

                data Id = Int
                data Found = { id: Id }
                data Missing = { asked: Id }

                behavior lookup : (id: Id) -> Found | Missing
                    ensures positive = Missing -> id.value > 0

                data Placed = { by: Id }

                behavior place : (id: Id) -> Placed
                    depends on lookup
                    constructs Placed

                let place (id, lookup) = match lookup(id) with
                    | Found   -> Placed { by = id }
                    | Missing -> Placed { by = id }

                fake lookup
                    | (Id(0)) -> Missing { asked = Id(0) }
                """, "Main"));

        assertTrue(codes.contains("E1929"), codes.toString());
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

    /**
     * What another module declares is checked with that module's contracts, and a fixture here has
     * none of them. The language does not admit one either: a {@code fake} names an injection target
     * of its own module, and a behavior another module declares is not one — so this is refused
     * before anything would be held.
     *
     * <p>Written down because the check's own refusal rests on it. {@code EnsuresChecks} holds one
     * module's contracts and raises rather than answering "declares nothing" when asked about
     * another module's behavior, so the day this refusal is lifted the fixture side has to be given
     * that module's contracts rather than quietly passing everything.
     */
    @Test
    void aFakeForABehaviorAnotherModuleDeclaresIsNotAdmitted() {
        List<String> codes = codesOf(Compilation.ofSources(List.of("""
                module up exposing ( Id, Found, lookup )

                data Id = Int
                data Found = { id: Id }

                behavior lookup : (id: Id) -> Found
                    ensures asked = value.id.value == id.value
                """, """
                module down

                import up ( Id, Found, lookup )

                data Placed = { by: Id }

                behavior place : (id: Id) -> Placed
                    depends on lookup
                    constructs Placed

                let place (id, lookup) = Placed { by = lookup(id).id }

                fake lookup
                    | (Id(1)) -> Found { id = Id(2) }

                example place
                    | "placed for the one asked" : (Id(1)) -> Placed { by = Id(1) }
                """), ModulePath.EMPTY));

        assertTrue(codes.contains("E1908"),
                "`lookup` is not an injected behavior of `down`, so nothing stands in: " + codes);
        assertFalse(codes.contains("E1929"), "nothing was held against a contract this module has "
                + "none of: " + codes);
    }

    /**
     * A table with a refused row is not compared against the rows recorded for the behavior either.
     *
     * <p>The two diagnostics say incompatible things. <em>E1929</em> says the declaration decides and
     * the fake is the side that is wrong; <em>E1919</em> says two descriptions disagree and neither is
     * named as right. Said about one pair they contradict each other — so a table the declaration has
     * already ruled out answers nothing here, as a table that will not build does.
     */
    @Test
    void aRefusedTableIsNotComparedWithTheRowsRecordedForTheBehavior() {
        List<String> codes = codesOf(Compilation.ofSource("""
                module example.clash

                data Id = Int
                data Found = { id: Id }

                behavior lookup : (id: Id) -> Found
                    ensures asked = value.id.value == id.value

                fake lookup
                    | (Id(1)) -> Found { id = Id(2) }

                example lookup
                    | "found for the one asked" : (Id(1)) -> Found { id = Id(1) }
                """, "Main"));

        assertTrue(codes.contains("E1929"), "the fake states what the declaration rules out: " + codes);
        assertFalse(codes.contains("E1919"),
                "the declaration has already said which side is wrong: " + codes);
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

    /** The codes a multi-source compile says, in the order they were said. */
    private static List<String> codesOf(Compilation c) {
        c.answerEverything();
        List<String> codes = new ArrayList<>();
        c.diagnostics().values().stream().flatMap(List::stream)
                .forEach(d -> codes.add(d.diagnostic().code()));
        return codes;
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
