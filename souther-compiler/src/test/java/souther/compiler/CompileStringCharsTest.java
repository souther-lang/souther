package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import org.junit.jupiter.api.Test;

import java.util.Locale;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Character access without a {@code Char} type: a character is a one-code-point {@code String}.
 * {@code String.characters} lists them, {@code String.codePoints} lists the same split as integers,
 * and {@code String.toInt : Int | NotANumber} parses (Elm {@code String.toInt}'s {@code Maybe} as a
 * named case). Together with {@code String.matches} and {@code Int.floorMod} these turn a checksum
 * into a plain fold in a behavior — no digit table, no {@code partial} index recursion.
 *
 * <p>Both splits are total, so the empty string gives the empty list and a fold over it answers its
 * seed. Nothing here answers "the first code point": a caller wanting one takes it out of
 * {@code codePoints} with {@code List.get}, which is where every other absence comes from.
 */
class CompileStringCharsTest {

    private long runInt(String module, String behavior, Object input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", input);
        String cls = Character.toUpperCase(behavior.charAt(0)) + behavior.substring(1);
        Object b = loader.loadClass("demo." + cls + "$Impl").getDeclaredConstructor().newInstance();
        return (long) Codecs.encode(loader, "demo.Out", Codecs.apply(b, in));
    }

    @Test
    void codePointsReadTheDigitsOfAString() throws Exception {
        // 桁和: sum of digit values via a fold over the code points. A digit's value is its code
        // point less that of "0" — the零 helper reads that from the string itself rather than
        // writing 48, so the arithmetic says where the number comes from.
        String src = """
                module demo
                import List ( fold )
                data In = { s: String }
                data Out = Int
                behavior calc : (i: In) -> Out constructs Out
                let 零 = List.get(0, String.codePoints("0")) |> Option.withDefault(0)
                let calc (i) = Out(fold((acc, c) -> acc + (c - 零), 0, String.codePoints(i.s)))
                """;
        assertEquals(12L, runInt(src, "calc", Map.of("s", "129")));   // 1+2+9
        assertEquals(0L, runInt(src, "calc", Map.of("s", "")));       // no code points
    }

    @Test
    void bothSplitsCountCodePointsNotUtf16Units() throws Exception {
        String src = """
                module demo
                data In = { s: String }
                data Out = Int
                behavior calc : (i: In) -> Out constructs Out
                let calc (i) = Out(List.length(String.characters(i.s)))
                """;
        String codes = """
                module demo
                data In = { s: String }
                data Out = Int
                behavior calc : (i: In) -> Out constructs Out
                let calc (i) = Out(List.length(String.codePoints(i.s)))
                """;
        assertEquals(3L, runInt(src, "calc", Map.of("s", "a1z")));
        assertEquals(2L, runInt(src, "calc", Map.of("s", "🍎x")));   // one code point + one
        assertEquals(2L, runInt(src, "calc", Map.of("s", "𠮷田")));  // a supplementary-plane kanji

        // The two splits are the same split, so they always answer the same length — and it is the
        // length `String.length` answers, not the UTF-16 unit count the JVM stores.
        assertEquals(2L, runInt(codes, "calc", Map.of("s", "🍎x")));
        assertEquals(2L, runInt(codes, "calc", Map.of("s", "𠮷田")));
    }

    @Test
    void toIntParsesOrTakesTheNotANumberCase() throws Exception {
        String src = """
                module demo
                data In = { s: String }
                data Out = Int
                behavior parse : (i: In) -> Out constructs Out
                let parse (i) = match String.toInt(i.s) with
                    | Int as n -> Out(n)
                    | NotANumber -> Out(-1)
                """;
        assertEquals(42L, runInt(src, "parse", Map.of("s", "42")));
        assertEquals(7L, runInt(src, "parse", Map.of("s", "007")));   // leading zeros kept
        assertEquals(-5L, runInt(src, "parse", Map.of("s", "-5")));   // a leading sign parses
        assertEquals(-1L, runInt(src, "parse", Map.of("s", "12x")));  // NotANumber
        assertEquals(-1L, runInt(src, "parse", Map.of("s", "")));     // NotANumber
        assertEquals(-1L, runInt(src, "parse", Map.of("s", " 5")));   // surrounding space: NotANumber
        assertEquals(-1L, runInt(src, "parse", Map.of("s", "99999999999999999999")));  // > Int64: NotANumber
    }

    /** A wrong case name over the parse union names its members, not the type's internal form. */
    @Test
    void aWrongCaseOverTheParseUnionNamesItsMembers() {
        String src = """
                module demo
                data In = { s: String }
                data Out = Int
                behavior parse : (i: In) -> Out constructs Out
                let parse (i) = match String.toInt(i.s) with
                    | Some n -> Out(n)
                    | NotANumber -> Out(-1)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        String rendered = new HumanRenderer(false).render(e.diagnostic(), null, Locale.ENGLISH);
        assertTrue(rendered.contains("Int | NotANumber"), rendered);
        assertFalse(rendered.contains("Union["), "internal type form leaked:\n" + rendered);
    }

    @Test
    void theFirstCodePointComesOutThroughListGet() throws Exception {
        // There is no `firstCodePoint`. The absence an empty string has is the absence `List.get`
        // already answers with, so the caller decides what it means rather than reading a sentinel.
        String src = """
                module demo
                data In = { s: String }
                data Out = Int
                behavior calc : (i: In) -> Out constructs Out
                let calc (i) = Out(List.get(0, String.codePoints(i.s)) |> Option.withDefault(-1))
                """;
        assertEquals(-1L, runInt(src, "calc", Map.of("s", "")));    // nothing there: the default
        assertEquals(48L, runInt(src, "calc", Map.of("s", "0")));   // '0' is code point 48
    }

    // The Issue #52 payoff: a mod-10 check digit as a plain fold in a behavior — the invariant proves
    // all-digits (#51), so the digit value is total; no digit table, no `partial` recursion.
    private static final String CHECKSUM = """
            module demo
            import List ( fold )
            data 符号 = String invariant String.matches("[0-9]+", value)
            data 妥当
            data 不正
            behavior 検証 : (s: 符号) -> 妥当 | 不正 constructs 妥当, 不正
            let 零 = List.get(0, String.codePoints("0")) |> Option.withDefault(0)
            let 桁和 (s: String) = fold((acc, c) -> acc + (c - 零), 0, String.codePoints(s))
            let 検証 (s) = {
                guard Int.floorMod(桁和(s.value), 10) == 0 else 不正
                妥当
            }
            """;

    @Test
    void checksumValidatesInABehaviorWithNoBoilerplate() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(CHECKSUM), getClass().getClassLoader());
        Object behavior = loader.loadClass("demo.検証$Impl").getDeclaredConstructor().newInstance();
        // "12340" digit-sum 10 ≡ 0 mod 10 → 妥当; "12345" sum 15 → 不正.
        Object ok = Codecs.apply(behavior, Codecs.decoded(loader, "demo.符号", "12340"));
        Object bad = Codecs.apply(behavior, Codecs.decoded(loader, "demo.符号", "12345"));
        assertEquals("demo.妥当", ok.getClass().getName());
        assertEquals("demo.不正", bad.getClass().getName());
    }

    @Test
    void aCodePointFoldWorksWithoutImportViaQualifiedList() throws Exception {
        // Same fold, calling List.fold qualified (no import) — the seam works either way.
        String src = """
                module demo
                data In = { s: String }
                data Out = Int
                behavior calc : (i: In) -> Out constructs Out
                let calc (i) = Out(List.fold((acc, c) -> acc + c, 0, String.codePoints(i.s)))
                """;
        assertEquals(49L + 50L, runInt(src, "calc", Map.of("s", "12")));   // '1'=49, '2'=50
    }
}
