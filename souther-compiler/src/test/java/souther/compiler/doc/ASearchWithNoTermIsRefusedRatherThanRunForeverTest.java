package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A term of no characters is contained in every string and at every position, so a walk that
 * advances by the term's length never advances. Nothing downstream can recover from that: it is
 * not an exception a caller can catch, it is a session that stops answering.
 *
 * <p>Each test asks for the refusal and gets it as a returned answer, so a walk that never advances
 * is a test that never returns.
 */
class ASearchWithNoTermIsRefusedRatherThanRunForeverTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void theSpecificationAnswersAnEmptyTermAtOnce() {
        assertEquals(List.of(), SpecDocument.bundled().rank(""));
    }

    @Test
    void theCommandRefusesASearchWithNothingToSearchFor() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();

        int code = DocCommand.run(new String[]{"--search", "   "},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));

        assertEquals(2, code);
        assertTrue(err.toString(StandardCharsets.UTF_8).contains("needs a term"),
                err.toString(StandardCharsets.UTF_8));
    }

    @Test
    void theStdlibSearchRefusesTheSameWay() {
        ByteArrayOutputStream err = new ByteArrayOutputStream();

        int code = ApiCommand.run(new String[]{"--search", ""},
                new PrintStream(new ByteArrayOutputStream(), true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));

        assertEquals(2, code);
        assertTrue(err.toString(StandardCharsets.UTF_8).contains("needs a term"),
                err.toString(StandardCharsets.UTF_8));
    }

    @Test
    void aToolCallMissingItsRequiredArgumentIsRefusedAndTheSessionGoesOn() {
        List<JsonNode> answers = serve(
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":"
                        + "{\"name\":\"doc_search\",\"arguments\":{}}}",
                "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"tools/list\"}");

        assertEquals(2, answers.size(), "the missing argument did not stop the server answering");
        assertEquals(-32602, answers.getFirst().get("error").get("code").asInt(),
                "a required argument that is not there is an invalid parameter");
        assertTrue(answers.get(1).get("result").has("tools"), "the next request is served as usual");
    }

    @Test
    void anArgumentPresentButEmptyIsRefusedTheSameWay() {
        List<JsonNode> answers = serve(
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":"
                        + "{\"name\":\"doc_search\",\"arguments\":{\"term\":\"\"}}}",
                "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"ping\"}");

        assertEquals(2, answers.size());
        assertEquals(-32602, answers.getFirst().get("error").get("code").asInt());
        assertTrue(answers.get(1).has("result"));
    }

    @Test
    void argumentsThatAreNotAnObjectAreRefusedEvenWhenTheToolRequiresNothing() {
        List<JsonNode> answers = serve(
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":"
                        + "{\"name\":\"stdlib_api\",\"arguments\":\"not an object\"}}",
                "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"ping\"}");

        assertEquals(-32602, answers.getFirst().get("error").get("code").asInt(),
                "a tool with no required argument still has a shape its arguments must take");
        assertTrue(answers.get(1).has("result"));
    }

    @Test
    void anArgumentOfTheWrongShapeIsRefusedRatherThanCoerced() {
        List<JsonNode> answers = serve(
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":"
                        + "{\"name\":\"doc_read\",\"arguments\":{\"name\":{\"anchor\":\"purpose\"}}}}",
                "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"ping\"}");

        assertEquals(2, answers.size());
        assertEquals(-32602, answers.getFirst().get("error").get("code").asInt());
        assertTrue(answers.get(1).has("result"));
    }

    private List<JsonNode> serve(String... requests) {
        ByteArrayInputStream in = new ByteArrayInputStream(
                (String.join("\n", requests) + "\n").getBytes(StandardCharsets.UTF_8));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        McpServer.serve(in, out);
        return out.toString(StandardCharsets.UTF_8).lines().map(JSON::readTree).toList();
    }
}
