package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * When an answer runs out of what it was asked for, it says what to ask next. That line is only
 * worth printing if the reader it reaches can act on it, and the two readers act differently: one
 * is at a prompt with subcommands and flags, the other holds tools and their arguments. An MCP
 * client told to run `souther doc` is being sent to a shell it does not have.
 *
 * <p>Documents that describe the CLI still describe it — that is their subject. What is checked
 * here is what an answer offers as the next thing to do.
 */
class AnAnswerOffersOnlyWhatItsOwnCallerCanDoTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void aSectionThatIsNotThereOffersTheListingAsAToolCall() {
        String said = text(call("doc_read", "{\"name\":\"no-such-section\"}"));

        assertTrue(said.contains("`doc_read` with no `name` lists every section"), said);
        assertTrue(!said.contains("souther doc"), said);
    }

    @Test
    void aTopicThatIsNotThereOffersItTheSameWay() {
        String said = text(call("doc_read", "{\"name\":\"nosuchlib/nothing\"}"));

        assertTrue(said.contains("`doc_read` with no `name` lists every section and topic"), said);
        assertTrue(!said.contains("souther doc"), said);
    }

    @Test
    void aSearchThatFindsNothingOffersItTheSameWay() {
        String said = text(call("doc_search", "{\"term\":\"zzzznothingsaysthis\"}"));

        assertTrue(said.contains("`doc_read` with no `name` lists"), said);
        assertTrue(!said.contains("souther doc"), said);
    }

    @Test
    void aTruncatedSearchOffersACountTheClientCanPass() {
        String said = text(call("doc_search", "{\"term\":\"type\"}"));

        assertTrue(said.contains("`limit: 0` for all of them"), said);
        assertTrue(!said.contains("--limit"), "`--limit` is a flag no MCP client can write: " + said);
    }

    @Test
    void aSignatureDefersToItsModulesSourceAsAToolCall() {
        String said = text(call("stdlib_api", "{\"name\":\"String.length\"}"));

        assertTrue(said.contains("`stdlib_api {name: \"String\", source: true}` for what it means"), said);
        assertTrue(!said.contains("souther api"), said);
    }

    @Test
    void andWhatTheOfferNamesIsACallThatAnswers() {
        String offered = text(call("stdlib_api", "{\"name\":\"String.length\"}"));
        assertTrue(offered.contains("{name: \"String\", source: true}"), offered);

        JsonNode answer = call("stdlib_api", "{\"name\":\"String\",\"source\":true}");

        assertTrue(!answer.get("isError").asBoolean(), "the call the answer named is one that works");
    }

    @Test
    void aReaderAtAPromptIsStillOfferedTheSpellingsThatPromptHas() {
        ByteArrayOutputStream doc = new ByteArrayOutputStream();
        DocCommand.run(new String[]{"no-such-section"},
                new PrintStream(doc, true, StandardCharsets.UTF_8),
                new PrintStream(doc, true, StandardCharsets.UTF_8));
        ByteArrayOutputStream api = new ByteArrayOutputStream();
        ApiCommand.run(new String[]{"String.length"},
                new PrintStream(api, true, StandardCharsets.UTF_8),
                new PrintStream(api, true, StandardCharsets.UTF_8));

        assertTrue(doc.toString(StandardCharsets.UTF_8).contains("`souther doc` lists every section"),
                "the CLI text was adapted for the other caller, not taken away from this one");
        assertTrue(api.toString(StandardCharsets.UTF_8).contains("`souther api --source String`"),
                api.toString(StandardCharsets.UTF_8));
    }

    private String text(JsonNode result) {
        return result.get("content").get(0).get("text").asString();
    }

    private JsonNode call(String tool, String arguments) {
        return serve("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":{\"name\":\""
                + tool + "\",\"arguments\":" + arguments + "}}").getFirst().get("result");
    }

    private List<JsonNode> serve(String... requests) {
        ByteArrayInputStream in = new ByteArrayInputStream(
                (String.join("\n", requests) + "\n").getBytes(StandardCharsets.UTF_8));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        McpServer.serve(in, out);
        return out.toString(StandardCharsets.UTF_8).lines().map(JSON::readTree).toList();
    }
}
