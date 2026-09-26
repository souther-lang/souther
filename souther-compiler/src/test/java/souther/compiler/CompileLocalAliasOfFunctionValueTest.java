package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value answering a function, bound to a local name and applied through the name. The name is a
 * second name for the value, so applying it does what applying the value does.
 */
class CompileLocalAliasOfFunctionValueTest {

    private static final String ADDER = """
            let adder (n: Int) = (x) -> x + n

            let inc = adder(1)
            """;

    @Test
    void aLocalNameForAFunctionValueIsApplied() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module shop exposing ( use )

                %s
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let g = inc
                    g(n)
                }
                """.formatted(ADDER)));
    }

    @Test
    void aLocalNameWithTheTypeWrittenIsDecidedTheSame() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module shop exposing ( use )

                %s
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let g: (Int) -> Int = inc
                    g(n)
                }
                """.formatted(ADDER)));
    }

    @Test
    void aNameForTheNameIsApplied() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module shop exposing ( use )

                %s
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let g = inc
                    let h = g
                    h(n)
                }
                """.formatted(ADDER)));
    }

    @Test
    void theNameAnswersWhatTheValueAnswers() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module shop exposing ( Count, use )

                data Count = Int

                %s
                behavior use : (c: Count) -> Count constructs Count
                let use (c) = {
                    let g = inc
                    Count(g(c.value))
                }
                """.formatted(ADDER)), getClass().getClassLoader());
        Object behavior = Emitted.behavior(loader, "shop", "use").getDeclaredConstructor().newInstance();
        Object in = Codecs.decoded(loader, "shop.Count", 41L);

        assertEquals(42L, Codecs.encode(loader, "shop.Count", Codecs.apply(behavior, in)));
    }
}
