package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.ExampleMessage;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row naming a case the behavior's answer cannot be is E1904, whatever the answer's type is and
 * whether or not anything answers the behavior.
 *
 * <p>A number or a list is made of no case a row can name, so naming one there is naming a case the
 * answer cannot be, the same as naming a case outside a sum. Asked of what a value at the answer's
 * position can be, by the reading a stand-in is admitted by, before the expectation is built or
 * anything is applied: a unit case is not first built as though it stood in for the answer and then
 * reported as a value that could not be built.
 */
class ACaseTheAnswerCannotBeIsNotOneOfItsResultCasesTest {

    private static final String BASE = """
            module example.store

            data Found = { v: Int }
            data Missing

            behavior labels : (n: Int) -> List<Int>

            behavior counted : (n: Int) -> Int

            behavior countedDefined : (n: Int) -> Int
            let countedDefined (n) = n

            behavior find : (n: Int) -> Found | Missing
            """;

    private static void notOneOfTheResultCases(String rows, String named, String answers) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(BASE + rows),
                "the row names a case the answer cannot be");
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        Diagnostic d = e.diagnostics().get(0);
        assertEquals("E1904", d.code(), e.getMessage());
        assertInstanceOf(ExampleMessage.NotOneOfTheResultCases.class, d.said());
        assertEquals(named, ((ExampleMessage.NotOneOfTheResultCases) d.said()).expected());
        assertTrue(d.notes().stream().anyMatch(note ->
                        note.said() instanceof ExampleMessage.ItAnswersWithNoCase(String said)
                                && said.equals(answers)),
                "told the answer is made of no case: " + d.notes());
    }

    @Test
    void aCaseNamedWhereANumberIsAnsweredIsNotOneOfItsCases() {
        notOneOfTheResultCases("""
                example counted
                    | "found" : (1) -> Found
                """, "Found", "Int");
    }

    @Test
    void aCaseNamedWhereAListIsAnsweredIsNotOneOfItsCases() {
        notOneOfTheResultCases("""
                example labels
                    | "found" : (1) -> Found
                """, "Found", "List<Int>");
    }

    /** A construction names the case it builds, and is held to it the same way. */
    @Test
    void aConstructionOfACaseWhereANumberIsAnsweredIsNotOneOfItsCases() {
        notOneOfTheResultCases("""
                example counted
                    | "found" : (1) -> Found { v = 1 }
                """, "Found", "Int");
    }

    /** A unit case is a case like any other, and not a value that failed to build. */
    @Test
    void aUnitCaseNamedWhereANumberIsAnsweredIsNotOneOfItsCases() {
        notOneOfTheResultCases("""
                example counted
                    | "missing" : (1) -> Missing
                """, "Missing", "Int");
    }

    /** A behavior with a body is held to the same rule, before its body is applied. */
    @Test
    void aRowOfABehaviorWithABodyIsHeldToTheSameRule() {
        notOneOfTheResultCases("""
                example countedDefined
                    | "found" : (1) -> Found
                """, "Found", "Int");
    }

    /** A case of the answer's sum is one it can be, named alone or built. */
    @Test
    void aCaseOfTheAnswersSumIsOneOfItsCases() {
        Compiler.compile(BASE + """
                example find
                    | "a found" : (1) -> Found
                    | "missing" : (2) -> Missing
                    | "built" : (3) -> Found { v = 3 }
                """);
    }
}
