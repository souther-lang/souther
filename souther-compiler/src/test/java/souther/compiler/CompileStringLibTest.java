package souther.compiler;

import souther.compiler.diag.CompileException;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** The String standard library beyond length/trim/lowercase (spec 18.1). */
class CompileStringLibTest {

    @Test
    void appendOperatorUppercaseAndSubstringInABehavior() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( uppercase, substring )

                data Name = String
                data Greeting = String

                behavior greet : (n: Name) -> Greeting constructs Greeting

                let greet (n) = Greeting { value = "hi " ++ uppercase(substring(0, 3, n.value)) ++ "!" }
                """), getClass().getClassLoader());

        Object name = Codecs.decoded(loader, "demo.Name", "robert");
        Object behavior = loader.loadClass("demo.Greet" + "$Impl").getConstructor().newInstance();
        Object greeting = Codecs.apply(behavior, name);

        // Greeting has a single String field, so it is a newtype: encodes as bare Text
        assertEquals("hi ROB!", Codecs.encode(loader, "demo.Greeting", greeting));
    }

    @Test
    void appendFunctionAndConcatOfAList() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( append, concat )

                data In = { name: String, parts: List<String> }
                data Out = {
                    greeting: String
                    , joined: String
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    greeting = append("Hello, ", i.name),
                    joined = concat(i.parts)
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In",
                java.util.Map.of("name", "world", "parts", java.util.List.of("a", "b", "c")));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        java.util.Map<?, ?> m = (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals("Hello, world", m.get("greeting"), "append joins two strings in order");
        assertEquals("abc", m.get("joined"), "concat flattens a List<String> with no separator");
    }

    @Test
    void concatOfAnEmptyListIsTheEmptyString() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( concat )

                data In = { parts: List<String> }
                data Out = String

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { value = concat(i.parts) }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In",
                java.util.Map.of("parts", java.util.List.of()));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        // Out has a single String field, so it is a newtype: encodes as bare Text
        assertEquals("", Codecs.encode(loader, "demo.Out", out), "concat([]) is the empty string");
    }

    @Test
    void appendingAStringToAListIsRejected() {
        // `++` is Elm's appendable: two lists or two strings, never a mix (spec 18.1).
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Bad = String

                behavior run : (b: Bad) -> Bad constructs Bad

                let run (b) = Bad { value = b.value ++ [1] }
                """));
        assertTrue(e.getMessage().contains("two lists or two strings"),
                "the diagnostic should name both admissible operand shapes: " + e.getMessage());
    }

    @Test
    void splitJoinAndReplace() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( split, join, replace )

                data Raw = String
                data Out = {
                    parts: List<String>
                    , joined: String
                    , swapped: String
                }

                behavior run : (r: Raw) -> Out constructs Out

                let run (r) = Out {
                    parts = split(",", r.value),
                    joined = join("|", split(",", r.value)),
                    swapped = replace(",", ";", r.value)
                }
                """), getClass().getClassLoader());

        Object raw = Codecs.decoded(loader, "demo.Raw", "a,b,,c");
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, raw);

        java.util.Map<?, ?> m = (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(java.util.List.of("a", "b", "", "c"), m.get("parts"), "split keeps empty pieces");
        assertEquals("a|b||c", m.get("joined"));
        assertEquals("a;b;;c", m.get("swapped"));
    }

    @Test
    void wordsAndFromInt() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( words, fromInt )

                data In = {
                    text: String
                    , n: Int
                }
                data Out = {
                    tokens: List<String>
                    , label: String
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    tokens = words(i.text),
                    label = "item-" ++ fromInt(i.n)
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", java.util.Map.of("text", "  the  quick fox ", "n", 42L));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, in);

        java.util.Map<?, ?> m = (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out", out);
        assertEquals(java.util.List.of("the", "quick", "fox"), m.get("tokens"), "words splits on whitespace runs");
        assertEquals("item-42", m.get("label"));
    }

    @Test
    void startsWithAndEndsWithInAnInvariant() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( startsWith, endsWith )

                data Sku = String
                    invariant startsWith("X", value) && endsWith("Z", value)
                """), getClass().getClassLoader());
        assertTrue(Codecs.decode(loader, "demo.Sku", "XabcZ") instanceof Ok);
        assertTrue(Codecs.decode(loader, "demo.Sku", "Xabc") instanceof Err, "must end with Z");
        assertTrue(Codecs.decode(loader, "demo.Sku", "abcZ") instanceof Err, "must start with X");
    }

    /** {@code isEmpty} says "this text is blank" — the sibling of {@code List.isEmpty}. It reads the
     *  length, so a string of spaces is not blank; trim first to reject one. */
    @Test
    void isEmptyReadsBlankText() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( isEmpty, trim )
                import List ( filter )
                import Bool ( not )

                data In = { pieces: List<String> }
                data Out = { kept: List<String>, blank: Bool }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    kept = filter(p -> not(isEmpty(trim(p))), i.pieces),
                    blank = isEmpty("")
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In",
                java.util.Map.of("pieces", java.util.List.of("bug", " ", "", " ui ")));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        java.util.Map<?, ?> m =
                (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));

        assertEquals(java.util.List.of("bug", " ui "), m.get("kept"));
        assertEquals(true, m.get("blank"));
    }

    /** {@code reverse} / {@code repeat} / {@code lines} / {@code padLeft} / {@code padRight}: the rest
     *  of Elm's String module Souther's types allow. Padding is what builds a fixed-width identifier,
     *  so a code whose shape a newtype invariant states can be produced and not only checked. */
    @Test
    void reverseRepeatLinesAndPadding() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( reverse, repeat, lines, padLeft, padRight, fromInt )

                data In = { text: String, n: Int }
                data Out = {
                    turned: String
                    , rule: String
                    , none: String
                    , rows: List<String>
                    , bay: String
                    , right: String
                    , wide: String
                }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out {
                    turned = reverse("abc"),
                    rule = repeat(3, "-"),
                    none = repeat(0, "-"),
                    rows = lines(i.text),
                    bay = padLeft(4, "0", fromInt(i.n)),
                    right = padRight(4, ".", fromInt(i.n)),
                    wide = padLeft(2, "0", "12345")
                }
                """), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.In", java.util.Map.of("text", "a\r\nb\nc", "n", 7L));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        java.util.Map<?, ?> m =
                (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));

        assertEquals("cba", m.get("turned"));
        assertEquals("---", m.get("rule"));
        assertEquals("", m.get("none"), "a count of 0 or less repeats nothing");
        assertEquals(java.util.List.of("a", "b", "c"), m.get("rows"), "both \\r\\n and \\n break a line");
        assertEquals("0007", m.get("bay"));
        assertEquals("7...", m.get("right"));
        assertEquals("12345", m.get("wide"), "a string already that wide is left alone");
    }

    /** A count or width no JVM string could hold aborts rather than quietly producing something
     *  shorter than was asked for — the treatment an Int overflow gets (spec 18.2). */
    @Test
    void aRepeatCountOrPadWidthOutOfRangeAborts() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( repeat, padLeft )

                data In = { n: Int }
                data Out = { wide: String }

                behavior grow : (i: In) -> Out constructs Out
                behavior pad : (i: In) -> Out constructs Out

                let grow (i) = Out { wide = repeat(i.n, "x") }
                let pad (i) = Out { wide = padLeft(i.n, "0", "1") }
                """), getClass().getClassLoader());

        Object grow = loader.loadClass("demo.Grow" + "$Impl").getConstructor().newInstance();
        Object pad = loader.loadClass("demo.Pad" + "$Impl").getConstructor().newInstance();
        Object tooMany = Codecs.decoded(loader, "demo.In", java.util.Map.of("n", 3_000_000_000L));

        assertThrows(souther.runtime.ConstraintViolation.class, () -> Codecs.apply(grow, tooMany));
        assertThrows(souther.runtime.ConstraintViolation.class, () -> Codecs.apply(pad, tooMany));

        // An empty string repeats to nothing whatever the count, so there is nothing to abort over.
        BytesClassLoader empty = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( repeat )

                data In = { n: Int }
                data Out = { wide: String }

                behavior grow : (i: In) -> Out constructs Out

                let grow (i) = Out { wide = repeat(i.n, "") }
                """), getClass().getClassLoader());
        Object growEmpty = empty.loadClass("demo.Grow" + "$Impl").getConstructor().newInstance();
        java.util.Map<?, ?> out = (java.util.Map<?, ?>) Codecs.encode(empty, "demo.Out",
                Codecs.apply(growEmpty, Codecs.decoded(empty, "demo.In",
                        java.util.Map.of("n", 3_000_000_000L))));
        assertEquals("", out.get("wide"));
    }

    /** {@code fromDecimal} renders in plain notation and keeps the scale the value carries;
     *  {@code toDecimal} parses back, answering {@code Decimal | NotANumber} as {@code toInt} does. */
    @Test
    void decimalRenderingAndParsing() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module demo

                import String ( fromDecimal )

                data In = { amount: Decimal, text: String }
                data Out = {
                    shown: String
                    , rounded: String
                    , scaled: String
                    , parsed: String
                }

                behavior run : (i: In) -> Out constructs Out

                let readBack (s: String): String = match String.toDecimal(s) with
                    | Decimal as d -> fromDecimal(d)
                    | NotANumber -> "-"

                let run (i) = Out {
                    shown = fromDecimal(i.amount),
                    rounded = fromDecimal(Decimal.round(i.amount, 1, HALF_UP)),
                    scaled = fromDecimal(Decimal.round(0.1m * 1000.0m, 0, HALF_UP)),
                    parsed = readBack(i.text)
                }
                """), getClass().getClassLoader());

        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        java.util.Map<?, ?> m = (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In",
                        java.util.Map.of("amount", new java.math.BigDecimal("1000.25"), "text", "12.50"))));

        assertEquals("1000.25", m.get("shown"), "the scale the value carries is kept");
        assertEquals("1000.3", m.get("rounded"));
        assertEquals("100", m.get("scaled"), "rounding to scale 0 leaves no decimal point");
        assertEquals("12.50", m.get("parsed"), "a parsed value carries the scale it was written with");

        java.util.Map<?, ?> bad = (java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, Codecs.decoded(loader, "demo.In",
                        java.util.Map.of("amount", new java.math.BigDecimal("1000"), "text", "12x"))));
        assertEquals("1000", bad.get("shown"), "a whole number carries no decimal point");
        assertEquals("-", bad.get("parsed"), "text that is not a number takes the NotANumber arm");
    }
}
