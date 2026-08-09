package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A shipped kernel may take a function, and states so in its declaration ([#stdlib], ADR-0053).
 *
 * <p>Typing one takes three steps, in this order: the context pins what it can, the value arguments
 * fix the rest, and a function argument is typed last — against parameter types the others have
 * settled, so a block written there has something to be checked at. The order is observable in the
 * diagnostics, which is what these pin.
 *
 * <p>The pin from the context is for the function argument's sake. Where a kernel takes none there
 * is nothing waiting on it, and pinning anyway answers an argument mismatch against the type the
 * position wanted rather than the one the declaration asks for.
 */
class CompileHigherOrderIntrinsicTest {

    private static Object run(String source, String data, Map<String, Object> in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source),
                CompileHigherOrderIntrinsicTest.class.getClassLoader());
        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        return Codecs.encode(loader, data, Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", in)));
    }

    /**
     * The list fixes the element type from a value argument, and the predicate is then checked at it.
     * Nothing about the position the call sits in is needed for that.
     */
    @Test
    void aValueArgumentFixesTheTypeTheFunctionArgumentIsCheckedAt() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run("""
                module demo

                data In = { xs: List<Int> }
                data Out = { found: Int, absent: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    found = Option.withDefault(0, List.find((x) -> x > 2, i.xs)),
                    absent = Option.withDefault(-1, List.find((x) -> x > 99, i.xs))
                }
                """, "demo.Out", Map.of("xs", List.of(1L, 3L, 5L)));

        assertEquals(3L, out.get("found"));
        assertEquals(-1L, out.get("absent"), "the kernel answers None when nothing matches");
    }

    /** A function whose parameter is used at a type the element does not have is told so. */
    @Test
    void aFunctionArgumentIsCheckedAtTheElementTypeTheListFixed() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { xs: List<Int> }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { n = Option.withDefault(0, List.find((x) -> x ++ "!", i.xs)) }
                """));
        assertTrue(e.getMessage().contains("Int") && e.getMessage().contains("String"),
                e.getMessage());
    }

    /**
     * `Option.map` answers what its function answers, so the option's element type reaches the
     * function's parameter and the function's result becomes the option's.
     */
    @Test
    void aFunctionArgumentSuppliesTheResultTypeOfTheCall() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run("""
                module demo

                data In = { xs: List<Int> }
                data Out = { described: String }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    described = Option.withDefault("none",
                        Option.map((n) -> String.fromInt(n), List.find((x) -> x > 2, i.xs)))
                }
                """, "demo.Out", Map.of("xs", List.of(1L, 7L)));

        assertEquals("7", out.get("described"));
    }

    /**
     * The context pins the accumulator before the step is read, which is the whole reason the pin
     * runs first. Seeded with a value whose type nothing else fixes, only the position says what the
     * fold grows.
     */
    @Test
    void theContextPinsWhatAFunctionArgumentIsCheckedAgainst() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run("""
                module demo

                data In = { xs: List<Int> }
                data Out = { counts: Map<String, Int> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    counts = List.fold((acc, x) -> Map.updateOrInsert(String.fromInt(x), 1, (n) -> n + 1, acc),
                        Map.empty, i.xs)
                }
                """, "demo.Out", Map.of("xs", List.of(1L, 1L, 2L)));

        assertEquals(Map.of("1", 2L, "2", 1L), out.get("counts"));
    }

    /**
     * A kernel taking no function has nothing waiting on the pin, so its own rule answers rather
     * than a unification against the type the position wanted. `List.sum` over a newtype reports
     * that it needs a numeric element — not that it expected a Decimal and got a `Hours`.
     */
    @Test
    void aKernelTakingNoFunctionIsNotPinnedByThePositionItSitsIn() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Hours = Decimal
                data In = { xs: List<Hours> }
                data Out = { total: Decimal }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { total = List.sum(i.xs) }
                """));
        assertTrue(e.getMessage().contains("`List.sum` needs a list of Int or Decimal"), e.getMessage());
    }

    /** A key answering something with no natural order is refused for what the key answers. */
    @Test
    void sortByRefusesAKeyThatAnswersNoOrder() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Pair = { a: Int, b: Int }
                data Item = { name: String, p: Pair }
                data In = { items: List<Item> }
                data Out = { names: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    names = List.map((it) -> it.name, List.sortBy((it) -> it.p, i.items))
                }
                """));
        assertTrue(e.getMessage().contains("ordered"), e.getMessage());
    }

    /**
     * The kernel applies the function; the emitter puts it on the stack once, before the container.
     * Getting that order wrong is bytecode that does not verify, so running the result is the check.
     */
    @Test
    void theFunctionIsPutOnTheStackBeforeTheContainerItWalks() throws Exception {
        Map<?, ?> out = (Map<?, ?>) run("""
                module demo

                data In = { xs: List<Int>, bump: Int }
                data Out = { sorted: List<Int>, first: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    sorted = List.sortBy((x) -> 0 - x, i.xs),
                    first = Option.withDefault(0, List.find((x) -> x > i.bump, i.xs))
                }
                """, "demo.Out", Map.of("xs", List.of(2L, 9L, 4L), "bump", 3L));

        assertEquals(List.of(9L, 4L, 2L), out.get("sorted"));
        assertEquals(9L, out.get("first"), "the capture reaches the kernel's Fn");
    }

    /**
     * A rounding mode is an ordinary value of the {@code RoundingMode} data, so an argument of
     * another type is an ordinary type mismatch naming the operation and the type it asks for.
     */
    @Test
    void aRoundingModeParameterIsTypedLikeAnyOther() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data In = { d: Decimal }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { n = Decimal.toInt(i.d, i.d) }
                """));
        assertTrue(e.getMessage().contains("Decimal.toInt"), e.getMessage());
        assertTrue(e.getMessage().contains("RoundingMode"), e.getMessage());
    }
}
