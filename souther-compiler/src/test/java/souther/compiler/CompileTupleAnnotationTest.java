package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A helper parameter may be annotated with a tuple type. It reads the same as a function type's
 * parameter list up to the closing paren, so the two are told apart by what follows it: `->` makes
 * it a function type, anything else a tuple. This is what lets a domain consume {@code Map.toList},
 * whose entries are {@code ('k, 'a)} pairs (destructured with {@code let (k, v) = e}).
 */
class CompileTupleAnnotationTest {

    @Test
    void aHelperTakesATupleParameter() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { counts: Map<String, Int> }
                data Out = { lines: List<String> }

                behavior run : (i: In) -> Out constructs Out

                let entry (e: (String, Int)): String = {
                    let (k, v) = e
                    k ++ "=" ++ String.fromInt(v)
                }

                let run (i) = Out { lines = List.map(entry, Map.toList(i.counts)) }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("counts", Map.of("a", 2L)));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(List.of("a=2"), out.get("lines"));
    }

    @Test
    void aFunctionTypedParameterStillParses() throws Exception {
        // The disambiguation must not break the existing form: `(Int) -> Bool` is a function type.
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { ns: List<Int> }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out

                let countBy (p: (Int) -> Bool, xs: List<Int>): Int = List.length(List.filter(p, xs))

                let run (i) = Out { n = countBy(x -> x > 1, i.ns) }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("ns", List.of(1L, 2L, 3L)));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(2L, out.get("n"));
    }

    @Test
    void aTupleReturnAnnotationParses() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { ns: List<Int> }
                data Out = { lo: Int, hi: Int }

                behavior run : (i: In) -> Out constructs Out

                let bounds (xs: List<Int>): (Int, Int) = (List.fold((a, x) -> if x < a then x else a, 0, xs),
                    List.fold((a, x) -> if x > a then x else a, 0, xs))

                let run (i) = {
                    let (lo, hi) = bounds(i.ns)
                    Out { lo = lo, hi = hi }
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", Map.of("ns", List.of(1L, 5L, 3L)));
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(0L, out.get("lo"));
        assertEquals(5L, out.get("hi"));
    }
}
