package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A sum all of whose cases are unit data carries nothing but which case it is, so it crosses the
 * boundary as that name — a bare string, the form every other serializer gives a fieldless
 * enumeration (serde, FSharp.SystemTextJson, Jackson, OpenAPI). Wrapping it in an object whose only
 * entry is the discriminator adds a level for nothing, and it is what kept such a sum out of key
 * position: a JSON object's key cannot be an object (issue #161, ADR-0040).
 */
class CompileUnitOnlySumBoundaryTest {

    private static final String STAGE_FIELD = """
            module demo

            data Stage = Prospecting | Won | Lost
            data In = { stage: Stage }
            data Out = { stage: Stage }

            behavior run : (i: In) -> Out constructs Out

            let run (i) = Out { stage = i.stage }
            """;

    private static Object run(BytesClassLoader loader, String in, String out, Object raw)
            throws Exception {
        Object decoded = Codecs.decoded(loader, in, raw);
        Object behavior = loader.loadClass("demo.Run$Impl").getConstructor().newInstance();
        return Codecs.encode(loader, out, Codecs.apply(behavior, decoded));
    }

    @Test
    void aUnitOnlySumIsAFieldsBareString() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(STAGE_FIELD), getClass().getClassLoader());

        assertEquals(Map.of("stage", "Won"),
                run(loader, "demo.In", "demo.Out", Map.of("stage", "Won")));
    }

    @Test
    void aUnitOnlySumKeysAMapAcrossTheBoundary() throws Exception {
        String src = """
                module demo

                data Stage = Prospecting | Won | Lost
                data In = { n: Int }
                data Out = { byStage: Map<Stage, Int> }

                behavior run : (i: In) -> Out constructs Out, Won

                let run (i) = Out { byStage = Map.singleton(Won, i.n) }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        assertEquals(Map.of("byStage", Map.of("Won", 3L)),
                run(loader, "demo.In", "demo.Out", Map.of("n", 3L)));
    }

    @Test
    void theJsonDecoderReadsTheSameBareString() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(STAGE_FIELD), getClass().getClassLoader());
        JsonNode node = JsonMapper.builder().build().readTree("{\"stage\":\"Lost\"}");

        assertInstanceOf(Ok.class, Codecs.decode(loader, "demo.In", "jsonDecoder", node));
    }

    @Test
    void aNameNoCaseAnswersToFailsTheDecode() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(STAGE_FIELD), getClass().getClassLoader());

        assertInstanceOf(Err.class, Codecs.decode(loader, "demo.In", Map.of("stage", "Closed")));
    }

    @Test
    void aSumWithOneFieldBearingCaseKeepsTheDiscriminatorObject() throws Exception {
        String src = """
                module demo

                data Won = { amount: Int }
                data Stage = Prospecting | Won
                data In = { stage: Stage }
                data Out = { stage: Stage }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = Out { stage = i.stage }
                """;
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        assertEquals(Map.of("stage", Map.of("type", "Prospecting")),
                run(loader, "demo.In", "demo.Out", Map.of("stage", Map.of("type", "Prospecting"))));
    }
}
