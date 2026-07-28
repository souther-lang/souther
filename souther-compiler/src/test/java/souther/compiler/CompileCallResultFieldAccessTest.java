package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A field is read off whatever produced it, not only off a name: `f(x).field` parses, so a newtype can
 * be opened on the call that builds it without an intervening `let` (issue #158).
 */
class CompileCallResultFieldAccessTest {

    private static Object apply(BytesClassLoader loader, String cls, Object in) throws Exception {
        Object b = loader.loadClass("demo." + cls + "$Impl").getConstructor().newInstance();
        return Codecs.apply(b, in);
    }

    @Test
    void aNewtypeIsOpenedOnTheCallThatBuildsIt() throws Exception {
        String src = """
                module demo
                exposing ( Amount, In, Out, run )

                data Amount = Int invariant value >= 0
                data In = { n: Int }
                data Out = { m: Int }

                let amountOf (i: In) = Amount(i.n)

                behavior run : (i: In) -> Out constructs Out, Amount

                let run (i) = Out { m = amountOf(i).value }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object out = apply(loader, "Run", Codecs.decoded(loader, "demo.In", java.util.Map.of("n", 7L)));

        assertEquals(7L, out.getClass().getMethod("m").invoke(out));
    }

    @Test
    void theChainKeepsGoingThroughSeveralFields() throws Exception {
        String src = """
                module demo
                exposing ( In, Out, run )

                data Address = { city: String }
                data Person = { address: Address }
                data In = { name: String }
                data Out = { c: String }

                let personOf (i: In) = Person { address = Address { city = i.name } }

                behavior run : (i: In) -> Out constructs Out, Person, Address

                let run (i) = Out { c = personOf(i).address.city }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object out = apply(loader, "Run", Codecs.decoded(loader, "demo.In", java.util.Map.of("name", "Kyoto")));

        assertEquals("Kyoto", out.getClass().getMethod("c").invoke(out));
    }

    @Test
    void anImportedTypesConstructorResultIsReachedInto() throws Exception {
        String up = """
                module up exposing ( Amount )

                data Amount = Int invariant value >= 0
                """;
        String down = """
                module down exposing ( In, Out, run )
                import up ( Amount )

                data In = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out, Amount

                let run (i) = Out { m = Amount(i.n).value }
                """;
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compileModules(java.util.List.of(up, down)), getClass().getClassLoader());
        Object b = loader.loadClass("down.Run$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(b, Codecs.decoded(loader, "down.In", java.util.Map.of("n", 3L)));

        assertEquals(3L, out.getClass().getMethod("m").invoke(out));
    }

    @Test
    void aMatchScrutineeReachesIntoACallResult() throws Exception {
        String src = """
                module demo
                exposing ( In, Out, run )

                data Held = { held: Int? }
                data In = { n: Int }
                data Out = { m: Int }

                let heldOf (i: In) = Held { held = i.n }

                behavior run : (i: In) -> Out constructs Out, Held

                let run (i) = Out { m = match heldOf(i).held with
                    | Some v -> v
                    | None -> 0
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object out = apply(loader, "Run", Codecs.decoded(loader, "demo.In", java.util.Map.of("n", 5L)));

        assertEquals(5L, out.getClass().getMethod("m").invoke(out));
    }

    /**
     * A bare `.field` is a getter (ADR-0055) and `x.field` is a read, and the two are told apart by
     * where they sit: a getter starts an expression, a read follows one. Extending the read to a call's
     * result puts them next to each other in an argument list, where the comma still separates them.
     */
    @Test
    void aBareGetterAfterACallArgumentStaysAGetter() throws Exception {
        String src = """
                module demo
                exposing ( In, Out, run )
                import List ( map, sum )

                data Amount = Int invariant value >= 0
                data In = { ns: List<Int> }
                data Out = { m: Int }

                let amountsOf (i: In) = map(n -> Amount(n), i.ns)
                let pick (xs: List<Amount>, f: (Amount) -> Int) = map(f, xs)

                behavior run : (i: In) -> Out constructs Out, Amount

                let run (i) = Out { m = sum(pick(amountsOf(i), .value)) }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object out = apply(loader, "Run",
                Codecs.decoded(loader, "demo.In", java.util.Map.of("ns", java.util.List.of(1L, 2L, 4L))));

        assertEquals(7L, out.getClass().getMethod("m").invoke(out));
    }
}
