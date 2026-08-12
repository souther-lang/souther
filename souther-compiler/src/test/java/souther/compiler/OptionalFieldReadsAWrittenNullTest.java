package souther.compiler;

import souther.cli.Runner;
import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Result;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import org.jooq.Field;
import org.jooq.Record;
import org.jooq.SQLDialect;
import org.jooq.impl.DSL;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code T?} field is {@code None} when the key is absent <em>and</em> when a value is written for
 * it that says there is none (spec §codec-generation): a JSON {@code null}, a map entry holding a null, a record
 * whose column is NULL. Only a value of some other shape is a failure.
 *
 * <p>A decoder is generated once per source, so a rule about reading holds or fails per source, and
 * it read a written null as a value to be decoded — the element decoder was handed it and reported
 * the field as required, which is what an optional field never is (issue #362). The rule was stated
 * in the specification, in two comments and in the javadoc of the test beside this one, and asserted
 * nowhere; every source is here so that the next source, or the next combinator, is not a fourth
 * place to state it.
 */
class OptionalFieldReadsAWrittenNullTest {

    @TempDir
    Path dir;

    private static final String MODULE = """
            module demo

            data Id = String
            data Trip = { id: Id, approver: Id? }
            """;

    private final JsonMapper mapper = JsonMapper.builder().build();

    private BytesClassLoader loader() {
        return new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
    }

    private static Object approverOf(Result<?> r) throws Exception {
        Object trip = ((Ok<?>) r).value();
        return trip.getClass().getMethod("approver").invoke(trip);
    }

    // === the three generated decoders ===

    @Test
    void theNeutralDecoderReadsANullEntryAsNone() throws Exception {
        BytesClassLoader loader = loader();
        Map<String, Object> raw = new HashMap<>();
        raw.put("id", "t-1");
        raw.put("approver", null);

        Result<?> r = Codecs.decode(loader, "demo.Trip", raw);

        assertInstanceOf(Ok.class, r, "an entry written null is None, not a failure");
        assertEquals("None", approverOf(r).getClass().getSimpleName());
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Trip", ((Ok<?>) r).value());
        assertFalse(out.containsKey("approver"), "and it encodes back as an omitted key");
    }

    @Test
    void theJsonDecoderReadsANullValueAsNone() throws Exception {
        JsonNode node = mapper.readTree("{\"id\":\"t-1\",\"approver\":null}");

        Result<?> r = Codecs.decode(loader(), "demo.Trip", "jsonDecoder", node);

        assertInstanceOf(Ok.class, r, "a JSON null is None, not a failure");
        assertEquals("None", approverOf(r).getClass().getSimpleName());
    }

    @Test
    void theRecordDecoderReadsANullColumnAsNone() throws Exception {
        Field<String> id = DSL.field(DSL.name("id"), String.class);
        Field<String> approver = DSL.field(DSL.name("approver"), String.class);
        Record record = DSL.using(SQLDialect.DEFAULT).newRecord(id, approver);
        record.set(id, "t-1");
        record.set(approver, null);

        Result<?> r = Codecs.decode(loader(), "demo.Trip", "recordDecoder", record);

        assertInstanceOf(Ok.class, r, "a NULL column is None, not a failure");
        assertEquals("None", approverOf(r).getClass().getSimpleName());
    }

    // === what is still a failure, and what it says ===

    @Test
    void aValueOfAnotherShapeStillFailsAndSaysWhatItWanted() throws Exception {
        JsonNode node = mapper.readTree("{\"id\":\"t-1\",\"approver\":42}");

        Result<?> r = Codecs.decode(loader(), "demo.Trip", "jsonDecoder", node);

        Err<?> err = assertInstanceOf(Err.class, r, "a number is not a value this field can hold");
        String message = err.issues().asList().getFirst().message();
        assertTrue(message.contains("string"), message);
        assertFalse(message.contains("required"),
                "an optional field is never required, so it must not be told it is");
    }

    @Test
    void aRequiredFieldWrittenNullIsStillRequired() throws Exception {
        JsonNode node = mapper.readTree("{\"id\":null,\"approver\":\"e-9\"}");

        Result<?> r = Codecs.decode(loader(), "demo.Trip", "jsonDecoder", node);

        Err<?> err = assertInstanceOf(Err.class, r, "`id` has no `?`, so a null is not a value for it");
        assertTrue(err.issues().asList().getFirst().message().contains("required"),
                "the message optional fields must not get is the one a required field does get");
    }

    // === end to end, the way it was reported ===

    @Test
    void runReadsANullOptionalFromTheInput() throws Exception {
        Path file = dir.resolve("opt.sou");
        Files.writeString(file, """
                module opt

                data Note = { body: String, tag: String? }

                behavior echo : (n: Note) -> Note

                let echo (n) = n
                """);

        assertEquals("{\"body\":\"b\"}",
                Runner.run(file, "echo", "{\"body\":\"b\",\"tag\":null}").trim());
        assertEquals("{\"body\":\"b\"}",
                Runner.run(file, "echo", "{\"body\":\"b\"}").trim(),
                "an absent key answers the same, which is what makes the two one case");
        assertEquals("{\"body\":\"b\",\"tag\":\"t\"}",
                Runner.run(file, "echo", "{\"body\":\"b\",\"tag\":\"t\"}").trim());

        RuntimeException e = assertThrows(Runner.RunException.class,
                () -> Runner.run(file, "echo", "{\"body\":\"b\",\"tag\":42}"));
        assertFalse(e.getMessage().contains("is required"), e.getMessage());
    }
}
