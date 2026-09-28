package souther.compiler;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A block is expanded where it is applied, and made a function value of its own only where a
 * position keeps what an expression answers: a binding, a return, an element of a list, a tuple or a
 * map, an argument handed to a function value. Each case here puts a function in one such position
 * and applies what was kept, so the case runs only where that position made the function a value.
 *
 * <p>{@code bump} is a value of the module whose body is a block, so a position that names it keeps
 * what the value's own method returns, and that method returns the block as a value too.
 * {@code adder} is a helper answering with a block, so a position that calls it is handed the block
 * itself, under the binding of its argument.
 */
class AFunctionAnswerIsMadeAValueWhereverItIsKeptTest {

    private static final String BUMP = "let bump: (Int) -> Int = (m) -> m + 1\n";

    private static final String ADDER = "let adder (k: Int) : (Int) -> Int = (m) -> m + k\n";

    @Test
    void aValueWhoseBodyIsABlockIsHeldAndApplied() throws Exception {
        assertEquals(12L, answer(BUMP + """
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let fs = [bump, bump]
                    List.fold((acc, f) -> f(acc), n, fs)
                }
                """, 10L));
    }

    @Test
    void aValueThatBindsBeforeItsBlockIsHeldAndApplied() throws Exception {
        assertEquals(15L, answer("""
                let shift: (Int) -> Int = {
                    let k = 5
                    (m) -> m + k
                }
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let fs = [shift]
                    List.fold((acc, f) -> f(acc), n, fs)
                }
                """, 10L));
    }

    @Test
    void aBlockInATupleIsApplied() throws Exception {
        assertEquals(13L, answer("""
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let p: (Int, (Int) -> Int) = (2, (m) -> m + 1)
                    let (k, f) = p
                    f(n) + k
                }
                """, 10L));
    }

    @Test
    void aTupleValueHoldingABlockIsApplied() throws Exception {
        assertEquals(13L, answer("""
                let pair: (Int, (Int) -> Int) = (2, (m) -> m + 1)
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let (k, f) = pair
                    f(n) + k
                }
                """, 10L));
    }

    @Test
    void aBlockHandedToAFunctionValueIsApplied() throws Exception {
        assertEquals(12L, answer("""
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let twice: ((Int) -> Int, Int) -> Int = (f, x) -> f(f(x))
                    let g = if n > 0 then twice else twice
                    g((m) -> m + 1, n)
                }
                """, 10L));
    }

    @Test
    void aMatchAnsweringABlockIsApplied() throws Exception {
        String source = """
                data Sign = Up | Down
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let s = if n > 0 then Up else Down
                    let f: (Int) -> Int = match s with
                        | Up -> (m) -> m + 1
                        | Down -> (m) -> m - 1
                    f(n)
                }
                """;
        assertEquals(11L, answer(source, 10L));
        assertEquals(-11L, answer(source, -10L));
    }

    @Test
    void aGuardAnsweringABlockIsApplied() throws Exception {
        String source = """
                data Pos = Int
                    invariant positive = value >= 1
                behavior use : (n: Int) -> Int
                    constructs Pos
                let use (n) = {
                    let f: (Int) -> Int = {
                        guard Pos(n) as p else (m) -> m
                        (m) -> m + p.value
                    }
                    f(n)
                }
                """;
        assertEquals(20L, answer(source, 10L));
        assertEquals(0L, answer(source, 0L));
    }

    @Test
    void aBlockInATupleOfThreeIsApplied() throws Exception {
        assertEquals(16L, answer(ADDER + """
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let (a, b, f) = (1, 2, adder(3))
                    f(n) + a + b
                }
                """, 10L));
    }

    @Test
    void aLambdaAnsweringABlockIsApplied() throws Exception {
        assertEquals(15L, answer(ADDER + """
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let outer: (Int) -> (Int) -> Int = (x) -> adder(x)
                    let g = if n > 0 then outer else outer
                    g(5)(n)
                }
                """, 10L));
    }

    @Test
    void aFoldWhoseAccumulatorIsABlockIsApplied() throws Exception {
        assertEquals(12L, answer(ADDER + """
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let f = List.fold((acc, x) -> adder(x), adder(0), [1, 2])
                    f(n)
                }
                """, 10L));
    }

    @Test
    void aListAFoldGrowsByABlockIsApplied() throws Exception {
        assertEquals(16L, answer(ADDER + """
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let fs = List.fold((acc, x) -> acc ++ [adder(x)], [], [1, 2, 3])
                    List.fold((acc, f) -> f(acc), n, fs)
                }
                """, 10L));
    }

    @Test
    void aListAppendedABlockIsApplied() throws Exception {
        assertEquals(13L, answer(ADDER + """
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let fs = [adder(1)] ++ [adder(2)]
                    List.fold((acc, f) -> f(acc), n, fs)
                }
                """, 10L));
    }

    @Test
    void aBlockARecursionHandsItselfInTailPositionIsApplied() throws Exception {
        // The function the last step hands over closed over the `n` of that step.
        assertEquals(1L, answer("""
                partial let loop (f: (Int) -> Int, n: Int): Int =
                    if n == 0 then f(0) else loop((x) -> x + n, n - 1)
                behavior use : (n: Int) -> Int
                let use (n) = loop((x) -> x, n)
                """, 10L));
    }

    @Test
    void aBlockHandedToAKernelThatKeepsItIsApplied() throws Exception {
        assertEquals(11L, answer(ADDER + """
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let fs = Map.insert(1, adder(1), Map.empty)
                    match Map.get(1, fs) with
                        | Some f -> f(n)
                        | None -> n
                }
                """, 10L));
    }

    @Test
    void aValueNamingAValueWhoseBodyIsABlockIsHeldAndApplied() throws Exception {
        assertEquals(11L, answer(BUMP + """
                let other: (Int) -> Int = bump
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let fs = [other]
                    List.fold((acc, f) -> f(acc), n, fs)
                }
                """, 10L));
    }

    @Test
    void aMapAFoldFillsWithBlocksIsApplied() throws Exception {
        assertEquals(12L, answer(ADDER + """
                behavior use : (n: Int) -> Int
                let use (n) = {
                    let fs = List.fold((acc, x) -> Map.insert(x, adder(x), acc), Map.empty, [1, 2])
                    match Map.get(2, fs) with
                        | Some f -> f(n)
                        | None -> n
                }
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
