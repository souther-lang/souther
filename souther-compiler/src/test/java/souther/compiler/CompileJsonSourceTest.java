package souther.compiler;

import net.unit8.raoh.Err;
import net.unit8.raoh.Issue;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;
import net.unit8.raoh.decode.Decoder;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Per-source decoder generation (spec §codec-generation): each data whose shape supports it gets a
 * {@code jsonDecoder()} (reads a Jackson {@code JsonNode}) and a {@code recordDecoder()}
 * (reads a jOOQ {@code Record}) beside the neutral {@code decoder()}. This exercises the
 * JSON source end-to-end; the jOOQ {@code $DecRecord} is loaded to verify its bytecode.
 */
class CompileJsonSourceTest {

    private static final String MODULE = """
            module demo
            import String ( length )

            data Account = {
                id: String
                , balance: Int
                , owner: String
            } invariant length(id) > 0

            data Submitted = { note: String }
            data Rejected = { reason: String }
            data Application = Submitted | Rejected
            """;

    private final JsonMapper mapper = JsonMapper.builder().build();

    private BytesClassLoader compile() {
        return new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
    }

    @Test
    void jsonDecoderReadsAJsonNodeObject() throws Exception {
        BytesClassLoader loader = compile();
        JsonNode node = mapper.readTree("{\"id\":\"acc-1\",\"balance\":100,\"owner\":\"bob\"}");
        Result<?> r = Codecs.decode(loader, "demo.Account", "jsonDecoder", node);

        assertInstanceOf(Ok.class, r, "a valid JSON object decodes to Ok");
    }

    @Test
    void jsonDecoderAccumulatesFieldErrors() throws Exception {
        BytesClassLoader loader = compile();
        // id is a number (expected string), balance is a string (expected long), owner is missing.
        JsonNode node = mapper.readTree("{\"id\":5,\"balance\":\"nope\"}");
        Result<?> r = Codecs.decode(loader, "demo.Account", "jsonDecoder", node);

        assertInstanceOf(Err.class, r);
        assertEquals(3, ((Err<?>) r).issues().asList().size(), "all three field errors accumulate");
    }

    @Test
    void jsonDecoderDiscriminatesASum() throws Exception {
        Result<?> r = Codecs.decode(compile(), "demo.Application", "jsonDecoder",
                mapper.readTree("{\"type\":\"Submitted\",\"note\":\"hi\"}"));

        assertInstanceOf(Ok.class, r);
        assertEquals("demo.Submitted", ((Ok<?>) r).value().getClass().getName());
    }

    @Test
    void jsonDecoderReadsTemporalFields() throws Exception {
        // A Date/DateTime field is read from a JSON string via Raoh's string().date()/dateTime(),
        // so a temporal-bearing type is JSON-decodable (previously its jsonDecoder was skipped).
        String src = """
                module demo
                data Event = { name: String, on: Date, at: DateTime }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        JsonNode node = mapper.readTree(
                "{\"name\":\"launch\",\"on\":\"2020-01-15\",\"at\":\"2020-01-15T09:30:00\"}");
        Result<?> r = Codecs.decode(loader, "demo.Event", "jsonDecoder", node);

        assertInstanceOf(Ok.class, r, "a JSON temporal string decodes to Ok");
    }

    @Test
    void jsonDecoderReadsATemporalNewtypeField() throws Exception {
        // a newtype over Date (a bare ISO string in JSON) exercises the prim-decoder leaf path too
        String src = """
                module demo
                data BornOn = Date
                data Person = { name: String, born: BornOn }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Result<?> r = Codecs.decode(loader, "demo.Person", "jsonDecoder",
                mapper.readTree("{\"name\":\"amy\",\"born\":\"1990-05-01\"}"));
        assertInstanceOf(Ok.class, r);
    }

    /** A node, the type read from it, and the one issue the node is reported as: where, and under
     *  which code. */
    private record Node(String why, String module, String type, String json, String path,
                        String code) {
    }

    /** A module declaring a record and a sum, which a node is read as and which hold one nested. */
    private static final String NESTED = """
            module demo
            data Note = { body: String, tag: String }
            data Envelope = { note: Note }
            data Submitted = { note: String }
            data Rejected = { reason: String }
            data Application = Submitted | Rejected
            data Wrapper = { content: Application }
            """;

    /**
     * A node that is not an object is one fact about the node, so it is reported once, where the
     * node is — and a null node is the absent value every other decoder calls required, not a shape
     * mismatch. Read field by field it becomes one issue per declared field, each blaming a field the
     * author wrote correctly: a four-field data turns one mistake into four reports. A sum is read
     * as an object too, its discriminator being a field, so the same rule holds for it; read through
     * the discriminator alone, the mismatch is blamed on the key the author had no chance to write.
     * Nested, the node is the record's own path and not its first field's.
     */
    @Test
    void jsonDecoderReportsANodeThatIsNotAnObjectOnceWhereItIs() throws Exception {
        List<Node> nodes = List.of(
                new Node("a record, not an object", MODULE, "Account", "5", "", "type_mismatch"),
                new Node("a record, null", MODULE, "Account", "null", "", "required"),
                new Node("a sum, not an object", MODULE, "Application", "5", "", "type_mismatch"),
                new Node("a sum, null", MODULE, "Application", "null", "", "required"),
                new Node("a record held in a record", NESTED, "Envelope", "{\"note\":5}", "/note", null),
                new Node("a sum held in a record", NESTED, "Wrapper", "{\"content\":5}", "/content",
                        null));
        for (Node each : nodes) {
            BytesClassLoader loader = new BytesClassLoader(Compiler.compile(each.module()),
                    getClass().getClassLoader());
            Result<?> r = Codecs.decode(loader, "demo." + each.type(), "jsonDecoder",
                    mapper.readTree(each.json()));

            assertInstanceOf(Err.class, r, each.why());
            List<Issue> issues = ((Err<?>) r).issues().asList();
            assertEquals(1, issues.size(), each.why() + ": one node, one issue: " + issues);
            assertEquals(each.path(), issues.get(0).path().toString(), each.why());
            if (each.code() != null) {
                assertEquals(each.code(), issues.get(0).code(), each.why());
            }
        }
    }

    /**
     * A data whose fields are all optional read a non-object as a record of absent fields and
     * succeeded: an optional field makes nothing of a node it cannot read, so no field objected.
     */
    @Test
    void jsonDecoderDoesNotReadANonObjectAsARecordOfAbsentFields() throws Exception {
        String src = """
                module demo
                data Draft = { body: String?, tag: String? }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());

        assertInstanceOf(Ok.class,
                Codecs.decode(loader, "demo.Draft", "jsonDecoder", mapper.readTree("{}")));
        assertInstanceOf(Err.class,
                Codecs.decode(loader, "demo.Draft", "jsonDecoder", mapper.readTree("5")));
    }

    @Test
    void recordDecoderBytecodeLoadsAndVerifies() throws Exception {
        // Constructing a standalone jOOQ Record needs the full jOOQ runtime, so here we just force
        // the $DecRecord class to load — that verifies its whole bytecode is valid.
        Object recordDecoder = Codecs.decoder(compile(), "demo.Account", "recordDecoder");
        assertInstanceOf(Decoder.class, recordDecoder);
    }
}
