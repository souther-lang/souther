package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A tuple carries several values through a computation and has no external form, so it is refused
 * where one is required: a data field, a newtype's base, and a behavior's input and output. Which
 * position refused it is part of the answer, so each names what it is that cannot hold a tuple.
 */
class CompileTupleBoundaryTest {

    private String refused(String module) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(module));
        String message = e.getMessage();
        assertTrue(message.contains("tuple"), message);
        return message;
    }

    @Test
    void aDataFieldTakesNoTuple() {
        String message = refused("""
                module demo

                data Row = { pair: (String, String) }
                """);
        assertTrue(message.contains("Row.pair"), message);
    }

    @Test
    void aNewtypeBaseTakesNoTuple() {
        refused("""
                module demo

                data Key = (String, String)
                """);
    }

    @Test
    void aBehaviorInputTakesNoTuple() {
        String message = refused("""
                module demo

                data Out = { a: String }

                behavior go : (p: (String, String)) -> Out
                    constructs Out
                let go (p) = {
                    let (x, _) = p
                    Out { a = x }
                }
                """);
        assertTrue(message.contains("p"), message);
    }

    @Test
    void aBehaviorOutputTakesNoTuple() {
        String message = refused("""
                module demo

                data Req = { a: String }

                behavior go : (r: Req) -> (String, String)
                let go (r) = (r.a, r.a)
                """);
        assertTrue(message.contains("go"), message);
    }

    @Test
    void aTupleNestedInACollectionIsRefusedToo() {
        refused("""
                module demo

                data Row = { pairs: List<(String, String)> }
                """);
    }

    @Test
    void aHelperSignatureMayCarryATuple() {
        Compiler.compile("""
                module demo

                data Req = { a: String }
                data Out = { a: String }

                let split (r: Req) : (String, String) = (r.a, r.a)

                behavior go : (r: Req) -> Out
                    constructs Out
                let go (r) = {
                    let (x, _) = split(r)
                    Out { a = x }
                }
                """);
    }
}
