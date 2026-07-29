package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A function value flows wherever its type may be written: what a name denotes does not depend on
 * the syntax that produced it. A lambda chosen at runtime is the same kind of value as a helper
 * named directly, and either may be handed to a combinator whose parameter is function-typed — once
 * the binding's type is known, by annotation or by an application the checker can read.
 */
class CompileFunctionValueFlowTest {

    private static final String ANNOTATED = """
            module demo

            data Order = { xs: List<Int>, spring: Bool }
            data Result = { ns: List<Int> }

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let f: (Int) -> Int = if o.spring then (x) -> x + 100 else (x) -> x + 1
                Result { ns = List.map(f, o.xs) }
            }
            """;

    @SuppressWarnings("unchecked")
    private List<Long> run(BytesClassLoader loader, Object check, List<Long> xs, boolean spring)
            throws Exception {
        Object order = Codecs.decoded(loader, "demo.Order", Map.of("xs", xs, "spring", spring));
        Object r = Codecs.apply(check, order);
        return (List<Long>) ((Map<?, ?>) Codecs.encode(loader, "demo.Result", r)).get("ns");
    }

    @Test
    void anAnnotatedFunctionValueIsPassedToACombinator() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(ANNOTATED), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check" + "$Impl").getDeclaredConstructor().newInstance();

        assertEquals(List.of(110L, 120L), run(loader, check, List.of(10L, 20L), true));
        assertEquals(List.of(11L, 21L), run(loader, check, List.of(10L, 20L), false));
    }
}
