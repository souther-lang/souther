package souther.compiler;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther examples}: what a migration reads while it is working.
 *
 * <p>The JSON is checked against the schema shipped beside it, because a build reads this and a build
 * cannot notice a key that quietly changed name.
 */
class MainExamplesSubcommandTest {

    private static final String MODEL = """
            module example.trip
            import String ( length )

            data MemberId = String
                invariant length(value) > 0

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Rejected = { reason: String }
            data Found = { id: MemberId }
            data Missing = { reason: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            behavior submit : (request: Draft) -> Submitted | Rejected
                constructs Submitted, Rejected

            let submit (request) = {
                guard request.cost.value <= 100 else Rejected { reason = "over" }
                Submitted { cost = request.cost }
            }

            example findMember
                | "known"   : (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                | "unknown" : (MemberId("m-9")) -> Missing { reason = "none" }

            example submit
                | "within" : (Draft { cost = Amount(50) }) -> Submitted
            """;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static String run(String... extraArgs) throws Exception {
        Path file = Files.createTempDirectory("souther-examples").resolve("trip.sou");
        Files.writeString(file, MODEL);
        List<String> args = new ArrayList<>(List.of("examples", file.toString()));
        args.addAll(List.of(extraArgs));

        PrintStream original = System.out;
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        System.setOut(new PrintStream(captured, true, StandardCharsets.UTF_8));
        try {
            Main.main(args.toArray(String[]::new));
        } finally {
            System.setOut(original);
        }
        return captured.toString(StandardCharsets.UTF_8);
    }

    @Test
    void theReportSaysWhichBehaviorsAreStillWaiting() throws Exception {
        String out = run();

        assertTrue(out.contains("findMember"), out);
        assertTrue(out.contains("injected"), out);
        assertTrue(out.contains("implemented"), out);
        assertTrue(out.contains("2 behaviors: 1 implemented, 1 injected; 2 rows waiting for a `let`."),
                out);
    }

    @Test
    void behaviorFiltersDownToOne() throws Exception {
        String out = run("--behavior", "submit");

        assertTrue(out.contains("submit"), out);
        assertFalse(out.contains("findMember"), out);
        assertTrue(out.contains("1 behavior: 1 implemented, 0 injected; 0 rows waiting"), out);
    }

    @Test
    void theJsonCarriesTheNumbersABuildReads() throws Exception {
        JsonNode root = JSON.readTree(run("--format", "json"));

        assertEquals(1, root.get("schemaVersion").asInt());
        assertEquals("complete", root.get("status").asString());
        assertNotNull(root.get("compilerVersion"));

        JsonNode module = root.get("modules").get(0);
        assertEquals("example.trip", module.get("module").asString());
        JsonNode findMember = module.get("behaviors").get(0);
        assertEquals("findMember", findMember.get("name").asString());
        assertEquals("injected", findMember.get("implementation").asString());
        assertEquals(2, findMember.get("rows").asInt());
        assertEquals(2, findMember.get("pending").asInt());

        JsonNode submit = module.get("behaviors").get(1);
        assertEquals("implemented", submit.get("implementation").asString());
        assertEquals(0, submit.get("pending").asInt());
    }

    /**
     * The shipped schema and what is actually emitted have to agree. Not a full validation — that
     * would want a library — but every key the schema requires is present and no key is emitted that
     * the schema does not declare, which is what drifts.
     */
    @Test
    void theEmittedJsonMatchesTheShippedSchema() throws Exception {
        JsonNode schema;
        try (var in = Main.class.getResourceAsStream("/souther/adequacy-schema-1.json")) {
            assertNotNull(in, "adequacy-schema-1.json ships beside the compiler");
            schema = JSON.readTree(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        }
        JsonNode root = JSON.readTree(run("--format", "json"));

        assertEquals(schema.get("properties").get("schemaVersion").get("const").asInt(),
                root.get("schemaVersion").asInt(), "a shape change raises the version");
        agrees(root, schema.get("properties"), schema.get("required"));

        JsonNode moduleDef = schema.get("$defs").get("module");
        JsonNode module = root.get("modules").get(0);
        agrees(module, moduleDef.get("properties"), moduleDef.get("required"));

        JsonNode behaviorDef = schema.get("$defs").get("behavior");
        agrees(module.get("behaviors").get(0), behaviorDef.get("properties"),
                behaviorDef.get("required"));
    }

    private static void agrees(JsonNode emitted, JsonNode properties, JsonNode required) {
        for (JsonNode key : required) {
            assertTrue(emitted.has(key.asString()),
                    "the schema requires `" + key.asString() + "` and it is not emitted");
        }
        for (String name : emitted.propertyNames()) {
            assertTrue(properties.has(name),
                    "`" + name + "` is emitted and the schema does not declare it");
        }
    }
}
