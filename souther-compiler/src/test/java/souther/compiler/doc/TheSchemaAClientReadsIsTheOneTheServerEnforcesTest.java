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

    /**
     * A schema's `integer` is a value that is whole, not a way of writing one down: 1, 1.0 and 1e0
     * are one number and all three are integers under it. So the boundary is fixed here as values
     * rather than as notations, and each is sent as well as read.
     */
    @Test
    void everyWayOfWritingACountIsAnsweredByWhetherTheCountIsInTheDomain() {
        assertCount("0", true);
        assertCount("1", true);
        assertCount("1.0", true);
        assertCount("1e0", true);
        assertCount("2147483647", true);
        assertCount("1.5", false);
        assertCount("-1", false);
        assertCount("2147483648", false);
        assertCount("\"1\"", false);
        assertCount("null", false);
    }

    /**
     * A number that no `double` holds is still the number that was sent. Rounding it on the way in
     * decides the question before anything gets to ask it: `1.0000000000000000001` becomes a count
     * the schema does not admit and would be honoured as `1`, and `1e-324` becomes zero, which is
     * this server's spelling for every hit there is.
     */
    @Test
    void aCountIsJudgedAsTheNumberSentAndNotAsWhatADoubleCanHold() {
        assertCount("1.0000000000000000001", false);
        assertCount("1e-324", false);
        assertCount("1e400", false);
    }

    /**
     * Both edges of the domain refuse, and a client that cannot tell which one it fell off does
     * not know whether to round the number or to make it smaller.
     */
    @Test
    void aCountOutsideTheDomainIsToldWhichEdgeItFellOff() {
        assertTrue(refusal("1.5").contains("whole number"), refusal("1.5"));
        assertTrue(refusal("2147483648").contains("2147483647"), refusal("2147483648"));
        assertFalse(refusal("2147483648").contains("whole number"),
                "2147483648 is whole; what it is not is small enough");
        assertTrue(refusal("1e400").contains("2147483647"),
                "1e400 is whole too, and taking it to a double would have called it otherwise");
    }

    @Test
    void aCountWrittenWithAPointIsReadAsTheCountAndNotMerelyAllowed() {
        String one = serve("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":{\"name\":"
                + "\"doc_search\",\"arguments\":{\"term\":\"newtype\",\"limit\":1.0}}}")
                .getFirst().get("result").get("content").get(0).get("text").asString();

        assertEquals(1, one.lines().filter(line -> line.contains("\t")).count(), one);
    }

    @Test
    void aStringArgumentPublishesThatEmptyIsNotOneOfItsValues() {
        JsonNode term = argument("doc_search", "term");

        assertEquals("string", term.get("type").asString());
        assertTrue(term.get("pattern").asString().startsWith("[^"),
                "the empty term is what the server refuses, so the schema says so before the call");
    }

    /**
     * `\s` is not one set. A schema's patterns are ECMA-262, where it takes in the no-break space;
     * Java's does not. Written either way, the same argument has to be answered the same way.
     */
    @Test
    void aSpaceIsASpaceOnBothSidesOfTheSchema() {
        String published = argument("doc_read", "name").get("pattern").asString();

        for (String space : List.of("\\u0020", "\\u00a0", "\\u2003", "\\ufeff")) {
            assertFalse(java.util.regex.Pattern.compile(published)
                            .matcher(unescape(space)).find(),
                    space + " is a space, so a string of only it says nothing");

            JsonNode answer = serve("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":"
                    + "{\"name\":\"doc_read\",\"arguments\":{\"name\":\"" + space + "\"}}}").getFirst();

            assertEquals(-32602, answer.get("error").get("code").asInt(),
                    space + " is refused by the server too, not only by the schema: " + answer);
        }
    }

    private String unescape(String escaped) {
        return String.valueOf((char) Integer.parseInt(escaped.substring(2), 16));
    }

    private String refusal(String written) {
        return count(written).get("error").get("message").asString();
    }

    private JsonNode count(String written) {
        return serve("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":{\"name\":"
                + "\"doc_search\",\"arguments\":{\"term\":\"newtype\",\"limit\":" + written + "}}}")
                .getFirst();
    }

    private void assertCount(String written, boolean inDomain) {
        JsonNode answer = count(written);

        assertEquals(inDomain, answer.has("result"), "limit: " + written + " -> " + answer);
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
                "{\"name\":\"doc_search\",\"arguments\":{\"term\":\"newtype\",\"limit\":1.0}}",
                "{\"name\":\"doc_search\",\"arguments\":{\"term\":\"newtype\",\"limit\":1e0}}",
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
