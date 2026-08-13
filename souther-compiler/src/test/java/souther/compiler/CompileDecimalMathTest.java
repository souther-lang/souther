package souther.compiler;

import net.unit8.raoh.Err;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;

import static org.junit.jupiter.api.Assertions.assertEquals;

/** Decimal arithmetic (spec §stdlib-decimal): add/subtract/multiply/compare as total operations. */
class CompileDecimalMathTest {

    @Test
    void addsAndMultipliesDecimals() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Decimal ( add, multiply )

                data Price = Decimal
                data Quote = { subtotal: Decimal, doubled: Decimal }

                behavior makeQuote : (a: Price, b: Price) -> Quote constructs Quote

                let makeQuote (a, b) = Quote {
                    subtotal = add(a.value, b.value),
                    doubled = multiply(add(a.value, b.value), a.value)
                }
                """), getClass().getClassLoader());

        Object a = Codecs.decoded(loader, "demo.Price", new BigDecimal("1.5"));
        Object b = Codecs.decoded(loader, "demo.Price", new BigDecimal("2.25"));

        Object behavior = Emitted.behavior(loader, "demo", "makeQuote").getConstructor().newInstance();
        Object quote = behavior.getClass()
                .getMethod("apply", Object.class, Object.class).invoke(behavior, a, b);

        java.util.Map<?, ?> out = (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Quote", quote);
        assertEquals(new BigDecimal("3.75"), out.get("subtotal"));
        assertEquals(new BigDecimal("5.625"), out.get("doubled")); // 3.75 * 1.5
    }

    @Test
    void comparesIntsInAnInvariant() throws Exception {
        // compare(a, b) yields -1/0/1; usable with the existing Int comparison operators
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import Int ( compare )

                data Ordered = {
                    lo: Int
                    , hi: Int
                } invariant compare(lo, hi) <= 0
                """), getClass().getClassLoader());
        assertEquals(false, Codecs.decode(loader, "demo.Ordered", java.util.Map.of("lo", 1L, "hi", 2L)) instanceof Err);
        assertEquals(true, Codecs.decode(loader, "demo.Ordered", java.util.Map.of("lo", 5L, "hi", 2L)) instanceof Err);
    }

    /** Elm's {@code Basics} arithmetic on both numeric types: {@code abs} makes a signed difference a
     *  distance, {@code min}/{@code max} are the two-value form of the comparison operators (the
     *  {@code List} pair answers an optional instead), and {@code clamp} holds a value in a range.
     *  All four are ordinary helpers — {@code <} and {@code -} already say it. */
    @Test
    void absMinMaxAndClampOverBothNumericTypes() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                data In = { n: Int, d: Decimal }
                data Out = {
                    distance: Int
                    , lower: Int
                    , upper: Int
                    , held: Int
                    , decDistance: Decimal
                    , decUpper: Decimal
                    , decHeld: Decimal
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    distance = Int.abs(i.n),
                    lower = Int.min(i.n, 0),
                    upper = Int.max(i.n, 0),
                    held = Int.clamp(1, 10, i.n),
                    decDistance = Decimal.abs(i.d),
                    decUpper = Decimal.max(i.d, 0.0m),
                    decHeld = Decimal.clamp(0.0m, 1.0m, i.d)
                }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        Object negOut = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In",
                java.util.Map.of("n", -3L, "d", new BigDecimal("-2.50"))));
        java.util.Map<?, ?> neg = (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out", negOut);

        assertEquals(3L, neg.get("distance"));
        assertEquals(-3L, neg.get("lower"));
        assertEquals(0L, neg.get("upper"));
        assertEquals(1L, neg.get("held"), "below the range, clamp answers the low bound");
        assertEquals(new BigDecimal("2.5"), neg.get("decDistance"));
        assertEquals(new BigDecimal("0"), neg.get("decUpper"));
        assertEquals(new BigDecimal("0"), neg.get("decHeld"));

        // These two are about the value and not about what a boundary writes. A boundary writes the
        // amount ([#primitives]) and shows no scale to read the claim off, so they are asked of the
        // value itself, which is where the scale still is.
        assertEquals(new BigDecimal("2.50"), read(negOut, "decDistance"), "negating keeps the scale");
        assertEquals(new BigDecimal("0.0"), read(negOut, "decHeld"),
                "clamp answers one of the three values written, never a re-scaled copy");

        java.util.Map<?, ?> big = (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In",
                        java.util.Map.of("n", 42L, "d", new BigDecimal("0.25")))));
        assertEquals(42L, big.get("distance"));
        assertEquals(10L, big.get("held"), "above the range, clamp answers the high bound");
        assertEquals(new BigDecimal("0.25"), big.get("decHeld"), "inside the range the value passes through");
    }

    /** A field of a generated data, read off the value rather than off what a boundary writes. */
    private static Object read(Object value, String field) throws Exception {
        return value.getClass().getMethod(field).invoke(value);
    }
}
