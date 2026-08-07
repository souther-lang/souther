package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code tools/list} publishes is the only account of these tools a client will ever get, so
 * it is a product of this server and not a description of one. Two ways it can be wrong: it can
 * invite a call the server then refuses, and it can hold back a form the server would have
 * answered. Both cost a client the same thing — a call spent learning what it was told.
 *
 * <p>So the schema is asserted as published text, and every domain it names is then sent.
 */
class TheSchemaAClientReadsIsTheOneTheServerEnforcesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void aCountIsPublishedAsACountAndNotMerelyAsANumber() {
        JsonNode limit = argument("doc_search", "limit");

        assertEquals("integer", limit.get("type").asString());
        assertEquals(0, limit.get("minimum").asInt(), "0 is all of them; below it means nothing");
        assertEquals(Integer.MAX_VALUE, limit.get("maximum").asInt(),
                "and above this the conversion the server performs cannot hold the value");
    }

    @Test
    void aStringArgumentPublishesThatEmptyIsNotOneOfItsValues() {
        JsonNode term = argument("doc_search", "term");

        assertEquals("string", term.get("type").asString());
        assertEquals("\\S", term.get("pattern").asString(),
                "the empty term is what the server refuses, so the schema says so before the call");
    }

    @Test
    void anArgumentTheServerCanDoWithoutIsNotPublishedAsRequired() {
        assertEquals(List.of("term"), required("doc_search"));
        assertEquals(List.of(), required("doc_read"), "no name is how the listing is asked for");
        assertEquals(List.of(), required("stdlib_api"));
        assertEquals(List.of("name"), required("stdlib_api_source"),
                "a module's source is read by naming the module, and there is nothing else to read");
        assertEquals(List.of("name"), required("jar_api"));
    }

    @Test
    void everyToolClosesTheSetOfArgumentsItTakes() {
        assertTrue(tools().valueStream().allMatch(
                        t -> !t.get("inputSchema").get("additionalProperties").asBoolean()),
                "so a client learns the arguments rather than trying them");
    }

    @Test
    void noToolLeavesAnArgumentsDomainToBeDiscoveredByCalling() {
        for (JsonNode tool : tools()) {
            JsonNode properties = tool.get("inputSchema").get("properties");
            for (String name : properties.propertyNames()) {
                assertTrue(properties.get(name).has("type"),
                        tool.get("name").asString() + "." + name + " says what it holds");
                assertTrue(properties.get(name).has("description"),
                        tool.get("name").asString() + "." + name + " says what it is for");
            }
        }
    }

    @Test
    void everyCallTheSchemaAdmitsIsOneTheServerAnswers() {
        List<String> admitted = List.of(
                "{\"name\":\"doc_read\"}",
                "{\"name\":\"doc_read\",\"arguments\":{}}",
                "{\"name\":\"doc_read\",\"arguments\":{\"name\":\"purpose\"}}",
                "{\"name\":\"doc_search\",\"arguments\":{\"term\":\"newtype\"}}",
                "{\"name\":\"doc_search\",\"arguments\":{\"term\":\"newtype\",\"limit\":0}}",
                "{\"name\":\"doc_search\",\"arguments\":{\"term\":\"newtype\",\"limit\":2147483647}}",
                "{\"name\":\"stdlib_api\",\"arguments\":{}}",
                "{\"name\":\"stdlib_api\",\"arguments\":{\"name\":\"List\"}}",
                "{\"name\":\"stdlib_api_search\",\"arguments\":{\"term\":\"map\"}}",
                "{\"name\":\"stdlib_api_source\",\"arguments\":{\"name\":\"String\"}}");

        for (String call : admitted) {
            JsonNode answer = serve("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\","
                    + "\"params\":" + call + "}").getFirst();

            assertTrue(answer.has("result"), call + " fits the published schema: " + answer);
            assertFalse(answer.get("result").get("isError").asBoolean(), call + " -> " + answer);
        }
    }

    private List<String> required(String tool) {
        return tools().valueStream().filter(t -> t.get("name").asString().equals(tool)).findFirst()
                .orElseThrow().get("inputSchema").get("required")
                .valueStream().map(JsonNode::asString).toList();
    }

    private JsonNode argument(String tool, String name) {
        return tools().valueStream().filter(t -> t.get("name").asString().equals(tool)).findFirst()
                .orElseThrow().get("inputSchema").get("properties").get(name);
    }

    private JsonNode tools() {
        return serve("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/list\"}")
                .getFirst().get("result").get("tools");
    }

    private List<JsonNode> serve(String... requests) {
        ByteArrayInputStream in = new ByteArrayInputStream(
                (String.join("\n", requests) + "\n").getBytes(StandardCharsets.UTF_8));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        McpServer.serve(in, out);
        return out.toString(StandardCharsets.UTF_8).lines().map(JSON::readTree).toList();
    }
}
