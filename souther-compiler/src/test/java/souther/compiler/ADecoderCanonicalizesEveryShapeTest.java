package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every shape a decoder can take canonicalizes the text it reads.
 *
 * <p>The first attempt at ADR-0096's canonicalization was a {@code .normalize()} written wherever a
 * string leaf happened to be built, and it missed four paths — a newtype's own base, a map's keys, a
 * sum's discriminator and an enumeration's name — each found separately and after the fact. Written
 * that way the property is "nobody forgot", which nothing checks and which grows a new way to be
 * wrong every time a decoder shape is added.
 *
 * <p>So the backend builds a text leaf in one place ({@code CodecGen.emitStringLeaf}) and this walks
 * the shapes. It asks what a caller sees rather than how the code is written: each case feeds the
 * decomposed spelling of one kana and expects the domain to hold the composed one. A shape added
 * later that does not come through the one leaf fails here.
 *
 * <p>The two encoder-side names — a sum's tag and an enumeration's case name — are checked too. They
 * are not arriving text but identifiers from a source file, and a decoder that canonicalizes what it
 * reads can only match them if they are canonical as well.
 */
class ADecoderCanonicalizesEveryShapeTest {

    /** か + a combining voiced sound mark: two code points. */
    private static final String NFD = "\u304b\u3099";
    /** The same kana as one code point. */
    private static final String NFC = "\u304c";

    /** The length the domain sees, for a module whose {@code calc} answers an Int. */
    private static long length(String module, Object input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module),
                ADecoderCanonicalizesEveryShapeTest.class.getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", input);
        Object behavior = loader.loadClass("demo.Calc$Impl").getDeclaredConstructor().newInstance();
        return (long) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
    }

    private static String module(String field, String expr) {
        return """
                module demo

                data In = { %s }
                data Out = Int

                behavior calc : (i: In) -> Out constructs Out

                let calc (i) = Out(%s)
                """.formatted(field, expr);
    }

    @Test
    void aPlainField() throws Exception {
        assertEquals(1L, length(module("s: String", "String.length(i.s)"), Map.of("s", NFD)));
    }

    @Test
    void anOptionalField() throws Exception {
        assertEquals(1L, length(module("s: String?",
                "i.s |> Option.map(v -> String.length(v)) |> Option.withDefault(-1)"),
                Map.of("s", NFD)));
    }

    @Test
    void aListElement() throws Exception {
        assertEquals(1L, length(module("xs: List<String>",
                "List.get(0, i.xs) |> Option.map(v -> String.length(v)) |> Option.withDefault(-1)"),
                Map.of("xs", List.of(NFD))));
    }

    @Test
    void aSetElement() throws Exception {
        // The set also collapses the two spellings into one member, which is what equivalent text is.
        assertEquals(1L, length(module("xs: Set<String>", "Set.size(i.xs)"),
                Map.of("xs", List.of(NFD, NFC))));
    }

    @Test
    void aMapValue() throws Exception {
        assertEquals(1L, length(module("m: Map<String, String>",
                "Map.get(\"k\", i.m) |> Option.map(v -> String.length(v)) |> Option.withDefault(-1)"),
                Map.of("m", Map.of("k", NFD))));
    }

    @Test
    void aMapKey() throws Exception {
        assertEquals(7L, length(module("m: Map<String, Int>",
                "Map.get(\"" + NFC + "\", i.m) |> Option.withDefault(-1)"),
                Map.of("m", Map.of(NFD, 7L))));
    }

    @Test
    void aNewtypesOwnBase() throws Exception {
        String module = """
                module demo

                data Name = String
                data In = { n: Name }
                data Out = Int

                behavior calc : (i: In) -> Out constructs Out

                let calc (i) = Out(String.length(i.n.value))
                """;
        assertEquals(1L, length(module, Map.of("n", NFD)));
    }

    @Test
    void aNewtypeUsedAsAMapKey() throws Exception {
        String module = """
                module demo

                data Key = String
                data In = { m: Map<Key, Int> }
                data Out = Int

                behavior calc : (i: In) -> Out constructs Out, Key

                let calc (i) = Out(Map.get(Key("%s"), i.m) |> Option.withDefault(-1))
                """.formatted(NFC);
        assertEquals(7L, length(module, Map.of("m", Map.of(NFD, 7L))));
    }

    @Test
    void aDiscriminatedSumsTag() throws Exception {
        // The case is named with the composed kana and the input carries the decomposed one.
        String module = """
                module demo

                data %s = { n: Int }
                data Other = { n: Int }
                data Shape = %s | Other
                data In = { s: Shape }
                data Out = Int

                behavior calc : (i: In) -> Out constructs Out

                let calc (i) = Out(match i.s with | %s as k -> k.n | Other as o -> 0 - o.n)
                """.formatted(NFC, NFC, NFC);
        Map<String, Object> tagged = new LinkedHashMap<>();
        tagged.put("type", NFD);
        tagged.put("n", 5L);
        assertEquals(5L, length(module, Map.of("s", tagged)),
                "a tag written decomposed still names the case written composed");
    }

    @Test
    void anEnumerationsCaseName() throws Exception {
        String module = """
                module demo

                data %s
                data Other
                data Flag = %s | Other
                data In = { f: Flag }
                data Out = Int

                behavior calc : (i: In) -> Out constructs Out

                let calc (i) = Out(match i.f with | %s -> 1 | Other -> 0)
                """.formatted(NFC, NFC, NFC);
        assertEquals(1L, length(module, Map.of("f", NFD)));
    }
}
