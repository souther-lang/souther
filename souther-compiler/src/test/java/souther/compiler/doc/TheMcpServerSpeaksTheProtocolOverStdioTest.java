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
    void aLegacyClientsOwnRevisionIsEchoedWhenItIsOneThisServerAnswersUnder() {
        List<JsonNode> answers = serve("""
                {"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"t","version":"0"}}}""");

        assertEquals("2025-06-18", answers.getFirst().get("result").get("protocolVersion").asString(),
                "a client on an older revision is answered on its own");
    }

    @Test
    void aRevisionThisServerDoesNotSpeakIsAnsweredWithTheNewestItDoes() {
        List<JsonNode> answers = serve("""
                {"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"1999-01-01","capabilities":{},"clientInfo":{"name":"t","version":"0"}}}""");

        assertEquals("2025-11-25", answers.getFirst().get("result").get("protocolVersion").asString(),
                "the server names what it does answer under, and lets the client decide");
    }

    @Test
    void anEraThisServerDoesNotImplementIsNotClaimedBackAtAClientThatAsksForIt() {
        List<JsonNode> answers = serve("""
                {"jsonrpc":"2.0","id":1,"method":"initialize","params":{"protocolVersion":"2026-07-28","capabilities":{},"clientInfo":{"name":"t","version":"0"}}}""");

        assertEquals("2025-11-25", answers.getFirst().get("result").get("protocolVersion").asString(),
                "the 2026 revisions settle the era in the opening exchange and carry each request's"
                        + " identity in an envelope this server does not read, so echoing one back"
                        + " would claim an era it cannot hold up");
    }

    @Test
    void aNotificationIsAnsweredWithSilence() {
        List<JsonNode> answers = serve(
                "{\"jsonrpc\":\"2.0\",\"method\":\"notifications/initialized\"}");

        assertEquals(0, answers.size());
    }

    @Test
    void toolsListNamesEveryAnswerAndTheirSchemas() {
        List<JsonNode> answers = serve("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"tools/list\"}");

        JsonNode tools = answers.getFirst().get("result").get("tools");
        List<String> names = tools.valueStream().map(t -> t.get("name").asString()).toList();
        assertEquals(List.of("doc_search", "doc_read", "stdlib_api", "stdlib_api_search",
                "stdlib_api_source", "jar_api"), names);
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

    /**
     * A tool schema is the whole of what a client can find out about a tool. A form the tool accepts
     * and the schema does not mention cannot be reached by a reader who only has the schema, so it
     * is missing however well it works.
     */
    @Test
    void theJarApiSchemaSaysThatAMemberCanBeSelected() {
        List<JsonNode> answers = serve("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"tools/list\"}");

        JsonNode jarApi = answers.getFirst().get("result").get("tools").valueStream()
                .filter(t -> t.get("name").asString().equals("jar_api")).findFirst().orElseThrow();
        assertTrue(jarApi.get("description").asString().contains("Class#member"),
                "the description names the form: " + jarApi.get("description").asString());
        String name = jarApi.get("inputSchema").get("properties").get("name")
                .get("description").asString();
        assertTrue(name.contains("#member"), "and so does the argument that takes it: " + name);
    }

    /**
     * A code is the one token in a banner that survives not being able to read the banner, and the
     * lookup it opens is how a reader answered in a language they do not read gets to an
     * explanation they do. That the code is a name this tool takes is a relation the compiler
     * holds over every code it prints; a client that has to infer it from a search hit is being
     * asked to rediscover something already guaranteed.
     */
    @Test
    void theDocReadSchemaSaysThatADiagnosticCodeIsAName() {
        List<JsonNode> answers = serve("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"tools/list\"}");

        JsonNode docRead = answers.getFirst().get("result").get("tools").valueStream()
                .filter(t -> t.get("name").asString().equals("doc_read")).findFirst().orElseThrow();
        String description = docRead.get("description").asString();
        assertTrue(description.contains("E2011"),
                "the description names the form a reader copies out of a banner: " + description);
        String name = docRead.get("inputSchema").get("properties").get("name")
                .get("description").asString();
        assertTrue(name.contains("diagnostic code"),
                "and so does the argument that takes it: " + name);
    }

    @Test
    void aDiagnosticCodeIsReadInTheSpellingTheBannerPrintsItIn() {
        List<JsonNode> answers = serve("""
                {"jsonrpc":"2.0","id":3,"method":"tools/call","params":{"name":"doc_read","arguments":{"name":"E2011"}}}""");

        JsonNode result = answers.getFirst().get("result");
        assertFalse(result.get("isError").asBoolean(), "the printed spelling is a name, not a mistake");
        assertTrue(result.get("content").get(0).get("text").asString()
                .contains("may violate its invariant"));
    }

    /**
     * A description is read by a client that has this server and nothing else. Sending it to a
     * command line for the rest of the answer names something it cannot reach, and it cannot tell
     * that from an answer it merely failed to find.
     */
    @Test
    void noToolSendsTheClientToAnAnswerThisServerDoesNotServe() {
        List<JsonNode> answers = serve("{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"tools/list\"}");

        for (JsonNode tool : answers.getFirst().get("result").get("tools").valueStream().toList()) {
            String description = tool.get("description").asString();
            assertFalse(description.contains("`souther"),
                    tool.get("name").asString() + " sends the client to a command it has no way to"
                            + " run: " + description);
        }
    }

    @Test
    void anUnknownMethodIsAJsonRpcError() {
        List<JsonNode> answers = serve("{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"nothing/here\"}");

        assertEquals(-32601, answers.getFirst().get("error").get("code").asInt());
    }
}
