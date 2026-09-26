package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.DiagnosticCode;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A definition that writes a function type is a value of that type, and a value is named where the
 * value it stands for would be written (spec §fn-declaration, §fn-value-semantics). Each case names
 * such a value as an argument, so it runs only where the name is read as the function it stands for
 * and not as the nullary definition it is lowered to.
 */
class AFunctionTypedValueIsThatTypeWhereItIsHandedOnTest {

    private static final String ADDER = "let adder (n: Int) = (x) -> x + n\n";

    private static final String APPLY = "let apply (f: (Int) -> Int, x: Int) = f(f(x))\n";

    @Test
    void aValueAnsweredByAHelperIsHandedToAHelper() throws Exception {
        assertEquals(20L, answer(ADDER + APPLY + """
                let bump: (Int) -> Int = adder(5)
                behavior use : (n: Int) -> Int
                let use (n) = apply(bump, n)
                """, 10L));
    }

    @Test
    void aValueWhoseBodyIsABlockIsHandedToAHelper() throws Exception {
        assertEquals(12L, answer(APPLY + """
                let bump: (Int) -> Int = (m) -> m + 1
                behavior use : (n: Int) -> Int
                let use (n) = apply(bump, n)
                """, 10L));
    }

    @Test
    void aValueWhoseBodyIsABlockIsAppliedTwice() throws Exception {
        assertEquals(12L, answer("""
                let bump: (Int) -> Int = (m) -> m + 1
                behavior use : (n: Int) -> Int
                let use (n) = bump(bump(n))
                """, 10L));
    }

    @Test
    void aValueWhoseBodyIsABlockIsAppliedInTwoBranches() throws Exception {
        String source = """
                let bump: (Int) -> Int = (m) -> m + 1
                behavior use : (n: Int) -> Int
                let use (n) = if n > 0 then bump(n) + bump(n) else bump(n)
                """;
        assertEquals(22L, answer(source, 10L));
        assertEquals(-9L, answer(source, -10L));
    }

    @Test
    void aValueThatIsNotAFunctionIsRefusedWhereAFunctionIsTaken() {
        CompileException refused = assertThrows(CompileException.class, () -> answer(APPLY + """
                let k: Int = 3
                behavior use : (n: Int) -> Int
                let use (n) = apply(k, n)
                """, 10L));
        assertEquals(DiagnosticCode.E1317.name(), refused.code());
        assertTrue(refused.getMessage().contains("but got Int"), refused.getMessage());
    }

    @Test
    void aValueAnsweredByAHelperIsHandedToAStandardLibraryFunction() throws Exception {
        assertEquals(List.of(15L, 16L), answer(ADDER + """
                let bump: (Int) -> Int = adder(5)
                behavior use : (n: Int) -> List<Int>
                let use (n) = List.map(bump, [n, n + 1])
                """, 10L));
    }

    /** What {@code use} in {@code module demo} with {@code body} answers for {@code n}. */
    private Object answer(String body, long n) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compile("module demo exposing ( use )\n" + body),
                getClass().getClassLoader());
        Object use = Emitted.behavior(loader, "demo", "use").getConstructor().newInstance();
        return Codecs.apply(use, n);
    }
}
