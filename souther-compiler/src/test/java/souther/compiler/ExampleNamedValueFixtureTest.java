package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The case a named fixture stands for is read through the value, not off the spelling of the name.
 *
 * <p>Where the position is a union written inline — a dependency returning {@code Account | NotFound} —
 * there is no decoder to dispatch on a tag, so the case has to come from the value the fixture names.
 * Reading it off the name found a type of that spelling or nothing, and a value's name is not a case
 * name, so a {@code fake} row and a {@code with} value could only be written inline (issue #206). The
 * expected side read a name as the case it asserts for the same reason.
 */
class ExampleNamedValueFixtureTest {

    private static final String LOOKUP = """
            module demo

            data Account  = { id: String }
            data NotFound
            data Answer   = { label: String }

            behavior lookUp : (key: String) -> Account | NotFound

            behavior labelOf : (key: String) -> Answer
                depends on lookUp
                constructs Answer

            let labelOf (key, lookUp) =
                match lookUp(key) with
                    | Account as a -> Answer { label = a.id }
                    | NotFound     -> Answer { label = "none" }

            let known = Account { id = "a-1" }
            """;

    @Test
    void aFakeRowMayNameAValueWhereTheOutputIsAUnion() {
        assertDoesNotThrow(() -> Compiler.compile(LOOKUP + """

                fake lookUp
                    | ("k") -> known
                    | _     -> NotFound

                example labelOf
                    | "found"   : ("k") -> Answer { label = "a-1" }
                    | "missing" : ("z") -> Answer { label = "none" }
                """));
    }

    @Test
    void aWithValueMayNameAValueWhereTheOutputIsAUnion() {
        assertDoesNotThrow(() -> Compiler.compile(LOOKUP + """

                example labelOf
                    | "found" : ("k") with lookUp = known -> Answer { label = "a-1" }
                """));
    }

    @Test
    void anExpectedValueMayBeNamed() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In  = { n: Int }
                data Out = { label: String }

                behavior run : (i: In) -> Out
                    constructs Out

                let run (i) = Out { label = "x" }

                let expected = Out { label = "x" }

                example run
                    | "a named expectation" : (In { n = 1 }) -> expected
                """));
    }

    @Test
    void aNamedExpectationStillHasToHold() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In  = { n: Int }
                data Out = { label: String }

                behavior run : (i: In) -> Out
                    constructs Out

                let run (i) = Out { label = "x" }

                let expected = Out { label = "y" }

                example run
                    | "a named expectation" : (In { n = 1 }) -> expected
                """));
        assertEquals("E1905", e.diagnostic().code());
        assertEquals("Out { label = \"y\" }", e.diagnostic().diff().expectedType(),
                "the expectation is shown as the value it names stands for");
    }

    @Test
    void aNamedExpectationMayStandForALiteral() {
        // A value naming no case has no case to show around it, and the failure says the value.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data In = { n: Int }

                behavior run : (i: In) -> Int

                let run (i) = 42

                let answer = 42

                example run
                    | "a named literal" : (In { n = 1 }) -> answer
                """));
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }

                behavior run : (i: In) -> Int

                let run (i) = 42

                let answer = 7

                example run
                    | "a named literal" : (In { n = 1 }) -> answer
                """));
        assertEquals("7", e.diagnostic().diff().expectedType());
    }

    @Test
    void aBareCaseNameStillAssertsOnlyTheCase() {
        // A name that denotes a case asserts the case and nothing about the value under it — the rule a
        // named value does not change.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Approved = { by: String }
                data Rejected = { why: String }
                data Verdict  = Approved | Rejected

                behavior judge : (n: Int) -> Verdict
                    constructs Approved
                    constructs Rejected

                let judge (n) =
                    if n >= 0 then Approved { by = "a" } else Rejected { why = "b" }

                example judge
                    | "positive" : (1)  -> Approved
                    | "negative" : (-1) -> Rejected
                """));
    }

    @Test
    void aNameThatDenotesNothingIsStillReportedWhereItIsWritten() {
        // Reading the expectation through the value it names does not move this report: nothing denotes
        // the name, which resolution says where the row is written, before an example is evaluated.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In  = { n: Int }
                data Out = { label: String }

                behavior run : (i: In) -> Out
                    constructs Out

                let run (i) = Out { label = "x" }

                example run
                    | "nothing denotes this" : (In { n = 1 }) -> nowhere
                """));
        assertTrue(e.getMessage().contains("nowhere"), e.getMessage());
    }
}
