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
 * A row of a behavior nothing in the compile answers, stating a value no answer can be, is refused
 * by the compile and not left for whatever runs an implementation later.
 *
 * <p>The row of a behavior with a body is refused for it by the comparison: whatever the body answers
 * is a value of the answer's type, and the stated value is not one. The row of an injected behavior
 * has no answer to compare, and waiting for one hands the finding to an output running a host's
 * implementation, outside any compile. So it is refused before it waits, by whether the value the row
 * states is a value of the answer's type at all.
 *
 * <p>Asked of the value and not of the type it was built at. Two collections of different element
 * types holding nothing are the same value to the comparison, so an empty one is never refused for
 * the type its elements would have had.
 */
class AStatedValueNoAnswerCanBeIsRefusedWhereNothingAnswersTest {

    private static final String BASE = """
            module example.store

            data Found = { v: Int }
            data Missing

            behavior labels : (n: Int) -> List<Int>

            behavior counted : (n: Int) -> Int

            behavior groups : (n: Int) -> List<List<Int>>

            behavior find : (n: Int) -> Found | Missing

            behavior groupsDefined : (n: Int) -> List<List<Int>>
            let groupsDefined (n) = []
            """;

    private static Diagnostic refused(String rows) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(BASE + rows),
                "the row states a value no answer can be");
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        Diagnostic d = e.diagnostics().get(0);
        assertEquals("E1905", d.code(), e.getMessage());
        assertInstanceOf(ExampleMessage.TheRowDoesNotHold.class, d.said());
        return d;
    }

    private static void saysNoAnswerIs(Diagnostic d, String stated, String answers) {
        assertTrue(d.notes().stream().anyMatch(note ->
                        note.said() instanceof ExampleMessage.NoAnswerIsWhatTheRowStates(
                                String said, String answered)
                                && said.equals(stated) && answered.equals(answers)),
                "the row is told it states " + stated + " where " + answers + " is answered: "
                        + d.notes());
    }

    @Test
    void aSetStatedWhereAListIsAnsweredIsRefused() {
        saysNoAnswerIs(refused("""
                example labels
                    | "a set stated where a list is answered" : (1) -> Set.fromList([1])
                """), "a set", "List<Int>");
    }

    @Test
    void anAmountStatedWhereANumberIsAnsweredIsRefused() {
        saysNoAnswerIs(refused("""
                example counted
                    | "an amount" : (1) -> 1.5m
                """), "Decimal", "Int");
    }

    /** At the depth the value has: an element that is a set, where each element is a list. */
    @Test
    void aSetHeldWhereEachElementIsAListIsRefused() {
        refused("""
                example groups
                    | "a set inside" : (1) -> [Set.fromList([1])]
                """);
    }

    /**
     * A list holding nothing is the list the behavior can answer with, whatever its elements would
     * have been — and a body answering with an empty list holds the same row, which is what keeps the
     * refusal no stricter than the comparison.
     */
    @Test
    void anEmptyListBuiltAsAListOfSetsIsNotRefused() {
        Compiler.compile(BASE + """
                example groups
                    | "nothing in it" : (1) -> List.take(0, [Set.fromList([1])])

                example groupsDefined
                    | "nothing in it" : (1) -> List.take(0, [Set.fromList([1])])
                """);
    }

    /**
     * A case and nothing under it, where the answer is not made of cases: a number or a list has none
     * a row can name, so no value of it is that case.
     */
    @Test
    void aCaseStatedWhereANumberIsAnsweredIsRefused() {
        saysNoAnswerIs(refused("""
                example counted
                    | "found" : (1) -> Found
                """), "Found", "Int");
    }

    @Test
    void aCaseStatedWhereAListIsAnsweredIsRefused() {
        saysNoAnswerIs(refused("""
                example labels
                    | "found" : (1) -> Found
                """), "Found", "List<Int>");
    }

    /** A value an answer can be waits for one, a list as much as a case of the answer's sum. */
    @Test
    void aValueAnAnswerCanBeIsNotRefused() {
        Compiler.compile(BASE + """
                example labels
                    | "a list" : (1) -> [1]

                example find
                    | "found" : (1) -> Found { v = 1 }
                    | "a found" : (2) -> Found
                    | "missing" : (3) -> Missing
                """);
    }
}
