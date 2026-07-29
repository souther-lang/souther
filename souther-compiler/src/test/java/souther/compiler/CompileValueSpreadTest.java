package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A spread names a value the same way any other position does. An {@code example} row and a behavior
 * body are the same language here: a record written with {@code ...base} in a row and the same record
 * written in a body must both reach the value {@code base} stands for.
 */
class CompileValueSpreadTest {

    private BytesClassLoader loader(String source) {
        return new BytesClassLoader(Compiler.compile(source), getClass().getClassLoader());
    }

    private static Object aged(BytesClassLoader loader) throws Exception {
        Object behavior = loader.loadClass("demo.Go$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("n", 1L)));
        return ((Map<?, ?>) Codecs.encode(loader, "demo.Person", out)).get("age");
    }

    @Test
    void aRecordValueMayBeSpreadInOrdinaryCode() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Person = { name: String, age: Int }

                let base = Person { name = "A", age = 20 }

                behavior go : (i: In) -> Person constructs Person
                let go (i) = Person { ...base, age = 21 }
                """);

        assertEquals(21L, aged(loader));
    }

    @Test
    void aChainOfRecordValuesMayBeSpread() throws Exception {
        BytesClassLoader loader = loader("""
                module demo

                data In = { n: Int }
                data Person = { name: String, age: Int }

                let origin = Person { name = "A", age = 20 }
                let base = Person { ...origin, name = "B" }

                behavior go : (i: In) -> Person constructs Person
                let go (i) = Person { ...base, age = 22 }
                """);

        assertEquals(22L, aged(loader));
    }

    /** A spread builds the value it copies, so what the value constructs is constructed here. */
    @Test
    void aValueSpreadContributesItsConstructions() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { n: Int }
                data Person = { name: String, age: Int }
                data Stamped = { name: String, age: Int }

                let base = Person { name = "A", age = 20 }

                behavior go : (i: In) -> Stamped constructs Stamped
                let go (i) = Stamped { ...base, age = 21 }
                """));

        assertTrue(e.getMessage().contains("constructs Person"), e.getMessage());
    }
}
