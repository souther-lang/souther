package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@code <} {@code <=} {@code >} {@code >=} on {@code String} compare the UTF-16 code-unit
 * sequence, not the code points {@link AStringIsMeasuredInCodePointsTest} measures {@code length},
 * {@code slice} and the rest of the module by (spec §equality, §string-code-points). The two orders
 * disagree wherever a surrogate pair sits beside a basic-plane character above it: {@code 𠮷} is
 * U+20BB7, one code point above {@code ￥} (U+FFE5), but written D842 DFB7 it begins with a unit
 * below {@code ￥}'s FFE5, so by code unit {@code 𠮷} is the smaller of the two.
 *
 * <p>This is the language-level contract, not the machinery underneath it —
 * {@code RuntimeOrder}'s own laws hold the compiler's automata to {@link String#compareTo}, which
 * is a check on that machinery rather than on what a Souther program's {@code <} means.
 */
class AStringIsOrderedByUtf16CodeUnitsTest {

    /** A supplementary-plane kanji: one code point, two UTF-16 units — D842 DFB7. */
    private static final String YOSHI = "𠮷";
    /** One code point, one UTF-16 unit — FFE5, below D842 but above D7FF. */
    private static final String YEN = "￥";

    private static final String MODULE = """
            module demo

            data In = { a: String, b: String }
            data Out = Bool

            behavior compare : (i: In) -> Out constructs Out

            let compare (i) = Out(%s)
            """;

    private static boolean compares(String expr, String a, String b) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE.formatted(expr)),
                getClass0());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("a", a, "b", b));
        Object behavior = Emitted.behavior(loader, "demo", "compare").getDeclaredConstructor()
                .newInstance();
        return (boolean) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    private static ClassLoader getClass0() {
        return AStringIsOrderedByUtf16CodeUnitsTest.class.getClassLoader();
    }

    @Test
    void aSupplementaryPlaneCharacterOrdersBelowABasicPlaneOneItsCodePointStandsAbove()
            throws Exception {
        assertEquals(true, compares("i.a < i.b", YOSHI, YEN),
                "code unit D842 is below FFE5, though code point U+20BB7 is above U+FFE5");
        assertEquals(false, compares("i.a > i.b", YOSHI, YEN));
    }

    @Test
    void orderingAgreesWithJavaLangStringCompareTo() throws Exception {
        assertEquals(YOSHI.compareTo(YEN) < 0, compares("i.a < i.b", YOSHI, YEN));
        assertEquals(YEN.compareTo(YOSHI) < 0, compares("i.a < i.b", YEN, YOSHI));
    }

    @Test
    void equalStringsOrderNeitherWay() throws Exception {
        assertEquals(false, compares("i.a < i.b", YOSHI, YOSHI));
        assertEquals(false, compares("i.a > i.b", YOSHI, YOSHI));
        assertEquals(true, compares("i.a <= i.b", YOSHI, YOSHI));
        assertEquals(true, compares("i.a >= i.b", YOSHI, YOSHI));
    }
}
