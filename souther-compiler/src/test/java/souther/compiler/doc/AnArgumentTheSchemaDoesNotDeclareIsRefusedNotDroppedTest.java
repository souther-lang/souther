package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An argument that is dropped costs a client more than one that is refused. The call comes back
 * with an answer, the answer is well formed, and nothing in it says the argument had no effect —
 * so a client reads the answer as the one it asked for and carries the wrong belief forward. A
 * client that has only these tools is the one most likely to guess a name, and the least able to
 * find out it guessed wrong.
 */
class AnArgumentTheSchemaDoesNotDeclareIsRefusedNotDroppedTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void anArgumentNoToolDeclaresIsRefusedAndTheOnesItDoesAreNamed() {
        JsonNode answer = call("doc_search", "{\"term\":\"newtype\",\"page\":2}");

        assertEquals(-32602, answer.get("error").get("code").asInt());
        String said = answer.get("error").get("message").asString();
        assertTrue(said.contains("`page`"), said);
        assertTrue(said.contains("`term`") && said.contains("`limit`"),
                "and the refusal says what there is instead: " + said);
    }

    @Test
    void aCountWrittenAsAStringIsRefusedRatherThanQuietlyIgnored() {
        JsonNode answer = call("doc_search", "{\"term\":\"/\",\"limit\":\"0\"}");

        assertEquals(-32602, answer.get("error").get("code").asInt(),
                "answering the default 20 here would look like the count was honoured");
        assertTrue(answer.get("error").get("message").asString().contains("must be an integer"));
    }

    @Test
    void aFlagWrittenAsAStringIsRefusedTheSameWay() {
        JsonNode answer = call("stdlib_api", "{\"name\":\"String\",\"source\":\"true\"}");

        assertEquals(-32602, answer.get("error").get("code").asInt());
        assertTrue(answer.get("error").get("message").asString().contains("must be true or false"));
    }

    @Test
    void aFlagThatNeedsANameIsRefusedRatherThanRunWithout() {
        JsonNode answer = call("stdlib_api", "{\"source\":true}");

        assertEquals(-32602, answer.get("error").get("code").asInt());
        assertTrue(answer.get("error").get("message").asString().contains("`source` needs `name`"),
                answer.get("error").get("message").asString());
    }

    @Test
    void anOptionalArgumentLeftOutIsNotAnErrorAtAll() {
        JsonNode answer = call("doc_read", "{}");

        assertTrue(answer.has("result"), "absent is how a client says it wants the whole listing");
    }

    @Test
    void theSessionGoesOnAfterEachRefusal() {
        List<JsonNode> answers = serve(
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":{\"name\":\"doc_read\","
                        + "\"arguments\":{\"offset\":1}}}",
                "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"ping\"}");

        assertEquals(2, answers.size());
        assertEquals(-32602, answers.getFirst().get("error").get("code").asInt());
        assertTrue(answers.get(1).has("result"));
    }

    private JsonNode call(String tool, String arguments) {
        return serve("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":{\"name\":\""
                + tool + "\",\"arguments\":" + arguments + "}}").getFirst();
    }

    private List<JsonNode> serve(String... requests) {
        ByteArrayInputStream in = new ByteArrayInputStream(
                (String.join("\n", requests) + "\n").getBytes(StandardCharsets.UTF_8));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        McpServer.serve(in, out);
        return out.toString(StandardCharsets.UTF_8).lines().map(JSON::readTree).toList();
    }
}
