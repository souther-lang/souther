package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.HumanRenderer;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a violated {@code ensures} records: which clause, what it was declared for, and what was
 * answered.
 *
 * <p>Two facts and not one. An arm may name a sum while an answer is one of its leaves, so the case
 * a rule was written for and the case the answer turned out to be are different things — and one
 * field carrying whichever came to hand told a reader "answering `Errors`" about an answer that was
 * a {@code NotFound}. The declaration's side is read where the check is emitted; the answer's side
 * is read from the answer.
 */
class AnEnsuresFailureSaysWhatItWasDeclaredForTest {

    /** An arm naming a sum, and an answer that is one of its leaves. */
    @Test
    void anArmNamingASumSaysBothTheArmAndTheLeafAnswered() {
        String said = renderedRefusal("""
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

        assertTrue(said.contains("positive, for Errors, answering NotFound"),
                "the clause, what it was declared for, and what was answered: " + said);
    }

    /** The same, where the row wrote the value rather than the case alone: the answer's case is read
     *  from the answer, and it is the leaf there too. */
    @Test
    void theArmAndTheLeafAreToldApartWhereTheRowWroteAValue() {
        String said = renderedRefusal("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound = { asked: Id }
                data Denied = { asked: Id }
                data Errors = NotFound | Denied

                behavior findTodo : (id: Id) -> Todo | Errors
                    ensures positive = Errors -> id.value > 0

                example findTodo
                    | "nothing is found for zero" : (Id(0)) -> NotFound { asked = Id(0) }
                """);

        assertTrue(said.contains("positive, for Errors, answering NotFound"), said);
    }

    /**
     * An arm naming the case that was answered says it once. The two facts are both there and are
     * the same one, and a message that spelled it twice would be saying nothing with the second.
     */
    @Test
    void anArmNamingTheCaseAnsweredSaysItOnce() {
        String said = renderedRefusal("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound = { asked: Id }

                behavior findTodo : (id: Id) -> Todo | NotFound
                    ensures positive = NotFound -> id.value > 0

                example findTodo
                    | "nothing is found for zero" : (Id(0)) -> NotFound
                """);

        assertTrue(said.contains("positive, answering NotFound"), said);
        assertFalse(said.contains("for NotFound"), "said once: " + said);
    }

    /**
     * The leaf that answered, and not the first one the arm has. Which leaf a value is comes from
     * the value, and a reading that stopped at the arm's first case would name a {@code NotFound}
     * every time this clause refused a {@code Denied}.
     *
     * <p>Nothing here counts the arm's cases either. What decides whether a case is recorded at all
     * is whether the clause's rule is guarded by one, which is settled where the arm is read — an
     * output with no cases admits no arm to write, and there is no sum with fewer than two.
     */
    @Test
    void theLeafRecordedIsTheOneAnswered() {
        String said = renderedRefusal("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound = { asked: Id }
                data Denied = { asked: Id }
                data Errors = NotFound | Denied

                behavior findTodo : (id: Id) -> Todo | Errors
                    ensures positive = Errors -> id.value > 0

                example findTodo
                    | "denied for zero" : (Id(0)) -> Denied
                """);

        assertTrue(said.contains("positive, for Errors, answering Denied"),
                "the second of the arm's leaves is the one that answered: " + said);
    }

    /**
     * The same read off a value: the row wrote a `Denied`, and what the answer is comes from
     * testing the arm's leaves against it rather than from where the row's text happened to stop.
     * The two readings answer alike, which is what keeps a run's abort and a row's refusal from
     * naming one answer two ways.
     */
    @Test
    void theLeafReadOffAValueIsTheOneAnswered() {
        String said = renderedRefusal("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }
                data NotFound = { asked: Id }
                data Denied = { asked: Id }
                data Errors = NotFound | Denied

                behavior findTodo : (id: Id) -> Todo | Errors
                    ensures positive = Errors -> id.value > 0

                example findTodo
                    | "denied for zero" : (Id(0)) -> Denied { asked = Id(0) }
                """);

        assertTrue(said.contains("positive, for Errors, answering Denied"), said);
    }

    /** An output with no cases: no arm may be written for it, so there is neither a case it was
     *  declared for nor a case the answer was. */
    @Test
    void anOutputWithNoCasesRecordsNeither() {
        String said = renderedRefusal("""
                module example.todo

                data Id = Int
                data Todo = { id: Id, title: String }

                behavior findTodo : (id: Id) -> Todo
                    ensures asked = value.id.value == id.value

                example findTodo
                    | "another id" : (Id(1)) -> Todo { id = Id(2), title = "write it" }
                """);

        assertTrue(said.contains("ensures not held on example.todo.findTodo: asked"), said);
        assertFalse(said.contains("answering"), "the answer has no cases: " + said);
        assertFalse(said.contains(" for "), "and no arm was written: " + said);
    }

    // --- harness --------------------------------------------------------------------------------

    private static String renderedRefusal(String model) {
        CompileException refused =
                assertThrows(CompileException.class, () -> Compiler.compile(model));
        for (Diagnostic d : refused.diagnostics()) {
            if ("E1928".equals(d.code())) {
                return new HumanRenderer(false).render(d, null, Locale.ENGLISH);
            }
        }
        List<String> codes = new ArrayList<>();
        for (Diagnostic d : refused.diagnostics()) {
            codes.add(d.code());
        }
        throw new AssertionError("no E1928 among " + codes);
    }
}
