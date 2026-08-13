package souther.compiler;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import org.junit.jupiter.api.Test;

/**
 * Values with no state are generated once and handed out, not allocated per use: a unit data (which
 * has no fields, no invariant and so no {@code __construct}), a lambda that captures nothing, and a
 * decoder/encoder implementation. {@code assertSame} is what proves it — the behaviour is otherwise
 * indistinguishable, which is exactly why the interning is safe.
 */
class CompileSharedInstanceTest {

    private static final String MODULE = """
            module demo

            data Mark
            data Flag = Bool
            data Tally = { n: Int }

            behavior marks : (f: Flag) -> List<Mark> constructs Mark
            let marks (f) = [Mark | f.value]

            behavior sumUp : (xs: List<Int>) -> Tally constructs Tally
            let sumUp (xs) = Tally { n = List.fold((acc, x) -> acc + x, 0, xs) }

            behavior firstPositive : (xs: List<Int>) -> Tally constructs Tally
            let firstPositive (xs) = Tally {
                n = match List.find(x -> x > 0, xs) with
                    | Some found -> found
                    | None -> 0
            }
            """;

    /** The module compiled once: the four tests only read, so they can share one loader. */
    private static final Map<String, byte[]> CLASSES = Compiler.compile(MODULE);
    private static final BytesClassLoader LOADER =
            new BytesClassLoader(CLASSES, CompileSharedInstanceTest.class.getClassLoader());

    private static BytesClassLoader compiled() {
        return LOADER;
    }

    /**
     * The {@code INSTANCE} field of the one synthetic lambda class in this module that interned
     * itself. The lambdas are asked for by number rather than picked out of the emitted names by
     * shape, since which number a lambda gets shifts whenever anything else emits one first. The
     * field is package-private, as every use site the compiler emits is in the module's own package.
     */
    private static Field interningLambdaField(BytesClassLoader loader) throws Exception {
        List<Field> found = new ArrayList<>();
        for (String name : Emitted.lambdas(CLASSES.keySet(), "demo")) {
            for (Field f : loader.loadClass(name).getDeclaredFields()) {
                if (f.getName().equals("INSTANCE")) {
                    f.setAccessible(true);
                    found.add(f);
                }
            }
        }
        assertEquals(1, found.size(), "expected exactly one interned lambda class, got " + found);
        return found.get(0);
    }

    @Test
    void aUnitDataHasExactlyOneValue() throws Exception {
        BytesClassLoader loader = compiled();
        Object flag = Codecs.decoded(loader, "demo.Flag", true);
        Object impl = Emitted.behavior(loader, "demo", "marks").getConstructor().newInstance();

        List<?> first = (List<?>) Codecs.apply(impl, flag);
        List<?> second = (List<?>) Codecs.apply(impl, flag);
        assertEquals(1, first.size());
        assertSame(first.get(0), second.get(0), "two constructions of a unit must be the same value");

        Object declared = loader.loadClass("demo.Mark").getField("INSTANCE").get(null);
        assertSame(declared, first.get(0), "the construction must load the type's one value");
    }

    @Test
    void aUnitDecoderYieldsTheSameValueAsConstructingIt() throws Exception {
        BytesClassLoader loader = compiled();
        Object declared = loader.loadClass("demo.Mark").getField("INSTANCE").get(null);
        assertSame(declared, Codecs.decoded(loader, "demo.Mark", java.util.Map.of()),
                "decoding a unit must yield the same value as constructing it");
    }

    @Test
    void aCodecFactoryHandsOutOneImplementation() throws Exception {
        BytesClassLoader loader = compiled();
        Class<?> tally = loader.loadClass("demo.Tally");
        assertSame(tally.getMethod("decoder").invoke(null), tally.getMethod("decoder").invoke(null),
                "decoder() must hand out one stateless implementation");
        assertSame(tally.getMethod("encoder").invoke(null), tally.getMethod("encoder").invoke(null),
                "encoder() must hand out one stateless implementation");
        assertSame(tally.getMethod("jsonDecoder").invoke(null), tally.getMethod("jsonDecoder").invoke(null));
    }

    @Test
    void aLambdaCapturingNothingIsGeneratedOnce() throws Exception {
        BytesClassLoader loader = compiled();
        // `x -> x > 0` closes over neither a local nor an injected behavior, so its class carries the
        // one instance every evaluation of that lambda loads. It is handed to `List.find`, which takes
        // its predicate as a value — a fold's step is not a lambda that escapes, being emitted as the
        // loop body where it stands. Found among the lambdas the module emitted, not by its number,
        // which shifts whenever anything else in the module emits one first.
        java.lang.reflect.Field instance = interningLambdaField(loader);
        assertSame(instance.get(null), instance.get(null));

        Object impl = Emitted.behavior(loader, "demo", "sumUp").getConstructor().newInstance();
        Object result = Codecs.apply(impl, List.of(1L, 2L, 3L));
        java.lang.reflect.Field n = result.getClass().getDeclaredField("n");
        n.setAccessible(true);
        assertEquals(6L, n.get(result));
    }
}
