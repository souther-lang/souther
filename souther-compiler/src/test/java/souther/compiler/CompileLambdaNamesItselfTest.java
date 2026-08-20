package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code let} does not bind its own name in its value (spec §let), so a name inside a lambda bound
 * by one is whatever that name was outside it.
 *
 * <p>The inliner used to hold declared helpers and let-bound lambdas in one table keyed by spelling,
 * where a lambda took the place of a declaration of the same name; a lambda whose body wrote its own
 * name would then have expanded into itself forever, and was refused for that reason. Held apart —
 * a declaration by the name it is reached by, a lambda by the binding it is bound to — the name
 * inside reaches what it always denoted, so there is nothing to refuse.
 */
class CompileLambdaNamesItselfTest {

    /** A lambda whose body writes its own name applies the helper of that name, and terminates. */
    @Test
    void aLambdaWritingItsOwnNameAppliesTheHelperOfThatName() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data Order = { v: Int }
                data Result = { n: Int }

                let twice (x: Int) = x * 2

                behavior check : (o: Order) -> Result
                    constructs Result

                let check (o) = {
                    let twice = (x) -> twice(x) + 1
                    Result { n = twice(o.v) }
                }
                """), getClass().getClassLoader());
        Object check = Emitted.behavior(loader, "demo", "check").getDeclaredConstructor().newInstance();
        Object order = Codecs.decoded(loader, "demo.Order", Map.of("v", 5L));
        Map<?, ?> result = (Map<?, ?>) Codecs.encode(loader, "demo.Result",
                Codecs.apply(check, order));
        assertEquals(11L, result.get("n"), "the inner `twice` is the helper: 5 * 2 + 1");
    }

    /** With no declaration of that name to reach, the name is reported where it is written. */
    @Test
    void aLambdaWritingANameNothingDeclaresIsReportedThere() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Order = { v: Int }
                data Result = { n: Int }

                behavior check : (o: Order) -> Result
                    constructs Result

                let check (o) = {
                    let step = (x) -> step(x) + 1
                    Result { n = step(o.v) }
                }
                """));
        assertTrue(e.getMessage().contains("step"), e.getMessage());
    }
}
