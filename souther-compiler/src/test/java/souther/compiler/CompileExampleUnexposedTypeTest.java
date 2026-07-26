package souther.compiler;

import org.junit.jupiter.api.Test;

/**
 * An {@code example} may use a type its module does not expose. {@code exposing} decides what leaves
 * a module, and an example does not leave it — the fixture is built and the result read back inside
 * the module being compiled. The fixture builder reached the generated codecs with
 * {@link Class#getMethod}, which sees only public members, so writing an {@code exposing} list for
 * one downstream import silently broke every example over a type that list did not mention.
 */
class CompileExampleUnexposedTypeTest {

    @Test
    void anExampleBuildsAFixtureOfATypeTheModuleDoesNotExpose() {
        Compiler.compile("""
                module demo exposing ( Out )

                data Code = String
                    invariant String.length(value) == 3
                data Out = { ok: Bool }

                behavior check : (c: Code) -> Out constructs Out

                let check (c) = Out { ok = String.startsWith("A", c.value) }

                example check
                  | "a code in the A series" : (Code("A01")) -> Out { ok = true }
                  | "a code outside it" : (Code("B01")) -> Out { ok = false }
                """);
    }

    @Test
    void anExampleReadsBackAnUnexposedOutput() {
        // the output is unexposed too, so the failure message's "actual" side has to encode it
        Compiler.compile("""
                module demo exposing ( In )

                data In = { n: Int }
                data Doubled = { n: Int }

                behavior twice : (i: In) -> Doubled constructs Doubled

                let twice (i) = Doubled { n = i.n * 2 }

                example twice
                  | "doubles" : (In { n = 3 }) -> Doubled { n = 6 }
                """);
    }

    @Test
    void anUnexposedCollectionElementIsBuiltToo() {
        Compiler.compile("""
                module demo exposing ( Out )

                data Tag = String
                data Out = { count: Int }

                behavior countTags : (tags: List<Tag>) -> Out constructs Out

                let countTags (tags) = Out { count = List.length(tags) }

                example countTags
                  | "two tags" : ([ Tag("a"), Tag("b") ]) -> Out { count = 2 }
                """);
    }
}
