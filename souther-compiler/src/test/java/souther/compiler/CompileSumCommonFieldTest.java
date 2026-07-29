package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What holds of every case is a property of the sum. When every case spreads the same data, the
 * fields that data contributes are readable on the sum itself — the spread is nominal, so the author
 * wrote the sharing down in each case and the compiler already checked it. A field that merely
 * happens to be named the same in every case is not shared (that reading would be structural, which
 * ADR-0012 declines), and stays the error it is today.
 */
class CompileSumCommonFieldTest {

    private static final String MODULE = """
            module demo

            data Common = { id: String }
            data Draft = { ...Common }
            data Sent = { ...Common, at: String }
            data Doc = Draft | Sent
            data Out = { id: String }

            behavior run : (d: Doc) -> Out constructs Out

            let run (d) = Out { id = d.id }
            """;

    private static String runWith(BytesClassLoader loader, Object raw) throws Exception {
        Object in = Codecs.decoded(loader, "demo.Doc", raw);
        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        return (String) ((Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, in))).get("id");
    }

    @Test
    void anImportedSumExposesTheSameFields() throws Exception {
        String docs = """
                module docs exposing ( Doc, Draft, Sent, Common )

                data Common = { id: String }
                data Draft = { ...Common }
                data Sent = { ...Common, at: String }
                data Doc = Draft | Sent
                """;
        String app = """
                module app
                import docs ( Doc )

                data Out = { id: String }

                behavior run : (d: Doc) -> Out constructs Out

                let run (d) = Out { id = d.id }
                """;
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compileModules(List.of(docs, app)), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "docs.Doc", Map.of("type", "Draft", "id", "d-1"));
        Object behavior = loader.loadClass("app.Run$Impl").getConstructor().newInstance();
        assertEquals("d-1", ((Map<?, ?>) Codecs.encode(loader, "app.Out",
                Codecs.apply(behavior, in))).get("id"));
    }

    @Test
    void anIntFieldIsReadWithTheDescriptorTheCaseRecordCarries() throws Exception {
        String src = """
                module demo

                data Common = { n: Int }
                data A = { ...Common }
                data B = { ...Common, s: String }
                data S = A | B
                data Out = { n: Int }

                behavior run : (s: S) -> Out constructs Out

                let run (s) = Out { n = s.n }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.S", Map.of("type", "A", "n", 7L));
        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        assertEquals(7L, ((Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, in))).get("n"));
    }

    @Test
    void aSpreadReachedThroughAnotherSpreadIsStillCommon() throws Exception {
        String src = """
                module demo

                data Common = { id: String }
                data Base = { ...Common, at: String }
                data Draft = { ...Base }
                data Sent = { ...Common, to: String }
                data Doc = Draft | Sent
                data Out = { id: String }

                behavior run : (d: Doc) -> Out constructs Out

                let run (d) = Out { id = d.id }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Doc",
                Map.of("type", "Draft", "id", "d-1", "at", "10:00"));
        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        assertEquals("d-1", ((Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, in))).get("id"));
    }

    @Test
    void aCaseThatIsItselfASumCarriesTheFieldThroughBothInterfaces() throws Exception {
        String src = """
                module demo

                data Common = { id: String }
                data Draft = { ...Common }
                data Sent = { ...Common, at: String }
                data Filed = { ...Common, by: String }
                data Closed = Sent | Filed
                data Doc = Draft | Closed
                data Out = { id: String }

                behavior run : (d: Doc) -> Out constructs Out

                let run (d) = Out { id = d.id }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        Object in = Codecs.decoded(loader, "demo.Doc",
                Map.of("type", "Filed", "id", "f-1", "by", "kawasima"));
        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        assertEquals("f-1", ((Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(behavior, in))).get("id"));
    }

    @Test
    void aFieldEveryCaseSpreadsIsReadOnTheSum() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());

        assertEquals("d-1", runWith(loader, Map.of("type", "Draft", "id", "d-1")));
        assertEquals("s-1", runWith(loader, Map.of("type", "Sent", "id", "s-1", "at", "10:00")));
    }
}
