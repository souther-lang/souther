package souther.compiler;

import souther.runtime.ConstraintViolation;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code ensures} is checked where the behavior answers.
 *
 * <p>The compiler does not prove that a body establishes its own clause — general relational
 * reasoning over a body is what ADR-0003 places outside the language — so what holds it is the check
 * that runs where the behavior answers. That is also what will make assuming the clause at a call
 * site sound: the same trade an {@code invariant} makes, assumed by readers and enforced by its
 * check.
 *
 * <p>A violation aborts. It is a model bug with no business name, so no case is added to any output
 * sum (spec §violation-destination) — the destination an invariant violation already has.
 */
class ABodyIsHeldToWhatItsBehaviorDeclaresTest {

    private static final String KEEPS_IT = """
            module demo

            data Amount = Int

            behavior twice : (a: Amount) -> Amount
                constructs Amount
                ensures doubled = value.value == a.value * 2

            let twice (a) = Amount { value = a.value * 2 }
            """;

    private static final String BREAKS_IT =
            KEEPS_IT.replace("Amount { value = a.value * 2 }", "Amount { value = a.value * 3 }");

    private static Object applied(String module, long input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module),
                ABodyIsHeldToWhatItsBehaviorDeclaresTest.class.getClassLoader());
        Object twice = Emitted.behavior(loader, "demo", "twice").getConstructor().newInstance();
        return Codecs.encode(loader, "demo.Amount",
                Codecs.apply(twice, Codecs.decoded(loader, "demo.Amount", input)));
    }

    @Test
    void aBodyThatEstablishesItsClauseAnswers() throws Exception {
        assertEquals(6L, applied(KEEPS_IT, 3), "3 * 2 = 6, which is what the clause states");
    }

    @Test
    void aBodyThatBreaksItsClauseAborts() {
        ConstraintViolation thrown =
                assertThrows(ConstraintViolation.class, () -> applied(BREAKS_IT, 3));

        assertTrue(thrown.getMessage().contains("demo.twice"),
                "the behavior whose declaration was not kept: " + thrown.getMessage());
        assertTrue(thrown.getMessage().contains("doubled"),
                "and the clause it was declared as: " + thrown.getMessage());
    }
}
