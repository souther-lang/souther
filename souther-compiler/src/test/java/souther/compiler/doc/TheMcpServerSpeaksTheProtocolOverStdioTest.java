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
 * `souther mcp` speaks MCP over stdio: newline-delimited JSON-RPC 2.0, one response line per
 * request, notifications answered with silence. The tools are the same answers the doc/api/japi
 * subcommands give — one implementation, reached over a second wire.
 */
class TheMcpServerSpeaksTheProtocolOverStdioTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private List<JsonNode> serve(String... requests) {
        ByteArrayInputStream in = new ByteArrayInputStream(
                (String.join("\n", requests) + "\n").getBytes(StandardCharsets.UTF_8));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        McpServer.serve(in, out);
        return out.toString(StandardCharsets.UTF_8).lines().map(JSON::readTree).toList();
    }

    @Test
    void initializeAnswersTheServersNameAndItsToolCapability() {
        List<JsonNode> answers = serve("""
                {"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"t","version":"0"}}}""");

        assertEquals(1, answers.size());
        JsonNode result = answers.getFirst().get("result");
        assertEquals("souther", result.get("serverInfo").get("name").asString());
        assertTrue(result.has("protocolVersion"));
        assertTrue(result.get("capabilities").has("tools"));
    }

    @Test
    void aNotificationIsAnsweredWithSilence() {
        List<JsonNode> answers = serve(
                "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\"}");

        assertEquals(0, answers.size());
    }

    @Test
    void toolsListNamesTheFourAnswersAndTheirSchemas() {
        List<JsonNode> answers = serve("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"tools/list\"}");

        JsonNode tools = answers.getFirst().get("result").get("tools");
        List<String> names = tools.valueStream().map(t -> t.get("name").asString()).toList();
        assertEquals(List.of("doc_search", "doc_read", "stdlib_api", "jar_api"), names);
        assertTrue(tools.valueStream().allMatch(t -> t.has("inputSchema")), "every tool declares its input");
    }

    @Test
    void toolsCallAnswersASpecSectionAsTextContent() {
        List<JsonNode> answers = serve("""
                {"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"doc_read","arguments":{"name":"purpose"}}}""");

        JsonNode result = answers.getFirst().get("result");
        assertTrue(result.get("content").get(0).get("text").asString().contains("JVM-targeted language"));
    }

    @Test
    void aToolAskedForNothingThatExistsSaysSoAsAToolErrorNotAProtocolError() {
        List<JsonNode> answers = serve("""
                {"jsonrpc":"2.0","id":4,"method":"tools/call","params":{"name":"doc_read","arguments":{"name":"no-such-section"}}}""");

        JsonNode result = answers.getFirst().get("result");
        assertTrue(result.get("isError").asBoolean(), "the failure belongs to the tool call");
        assertTrue(answers.getFirst().get("error") == null, "the protocol itself did not fail");
    }

    @Test
    void aToolThatBlowsUpIsAnsweredAndTheServerKeepsServing() throws Exception {
        java.nio.file.Path notAJar = java.nio.file.Files.createTempFile("not-a", ".jar");
        java.nio.file.Files.writeString(notAJar, "this is not a zip archive");

        List<JsonNode> answers = serve(
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":{\"name\":\"jar_api\","
                        + "\"arguments\":{\"name\":\"acme.Thing\",\"classpath\":\"" + notAJar + "\"}}}",
                "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"tools/list\"}");

        assertEquals(2, answers.size(), "the bad call did not take the server down with it");
        assertTrue(answers.getFirst().get("result").get("isError").asBoolean(),
                "the failure is the tool call's, not the server's");
        assertTrue(answers.get(1).get("result").has("tools"), "the next request is served as usual");
    }

    @Test
    void anUnknownMethodIsAJsonRpcError() {
        List<JsonNode> answers = serve("{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"nothing/here\"}");

        assertEquals(-32601, answers.getFirst().get("error").get("code").asInt());
    }
}
