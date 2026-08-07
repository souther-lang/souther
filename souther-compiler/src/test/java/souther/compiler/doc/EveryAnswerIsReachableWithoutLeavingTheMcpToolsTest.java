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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A client with these tools and nothing else has no shell, no repository and no listing of what
 * the tools reach. So every answer the commands can give has to have a spelling here: a capability
 * the table leaves out is one such a client can only arrive at by guessing a name, and a name it
 * cannot guess is content that does not exist for it.
 *
 * <p>These tests ask for each answer the way a client would have to, over the protocol, and hold
 * it against what the same command prints at a prompt.
 */
class EveryAnswerIsReachableWithoutLeavingTheMcpToolsTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Test
    void aClientThatKnowsNoNameIsGivenEveryNameThereIs() {
        String listing = text(call("doc_read", "{}"));

        assertEquals(printed(new String[]{}), listing,
                "the listing a reader gets for no argument is the listing a client gets for no name");
        assertTrue(listing.lines().count() > 300, "every section and every shipped topic, not a page of them");
        assertTrue(listing.contains("cli/start-here"),
                "including the topic written for a reader who has never written Souther");
    }

    @Test
    void everyNameTheListingGivesCanBeReadBack() {
        List<String> names = text(call("doc_read", "{}")).lines()
                .map(line -> line.substring(0, line.indexOf('\t'))).toList();

        for (int at : List.of(0, names.size() / 2, names.size() - 1)) {
            JsonNode answer = call("doc_read", "{\"name\":\"" + names.get(at) + "\"}");
            assertFalse(answer.get("isError").asBoolean(),
                    "`" + names.get(at) + "` was named by the listing, so it can be asked for");
        }
    }

    @Test
    void aSearchHoldsNothingBackWhenTheClientSaysNotTo() {
        String capped = text(call("doc_search", "{\"term\":\"/\"}"));
        String all = text(call("doc_search", "{\"term\":\"/\",\"limit\":0}"));

        assertTrue(capped.contains("more; "), "the default answer says it held some back");
        assertFalse(all.contains("more; "), "and the client can ask for those too");
        assertTrue(all.lines().count() > capped.lines().count(), all.lines().count() + " vs " + capped.lines().count());
    }

    @Test
    void aSearchAnswersTheCountItWasAskedFor() {
        String three = text(call("doc_search", "{\"term\":\"newtype\",\"limit\":3}"));

        assertEquals(3, three.lines().filter(line -> line.contains("\t")).count(),
                "three hits, whatever the default would have been");
    }

    @Test
    void aModulesOwnSourceIsAToolCallAway() {
        String source = text(call("stdlib_api", "{\"name\":\"String\",\"source\":true}"));

        assertEquals(printed(new String[]{"--source", "String"}), source);
        assertTrue(source.contains("String."), "the module's own declarations, not its signatures alone");
    }

    @Test
    void theStdlibCanBeSearchedAndNotOnlyListedOrNamed() {
        JsonNode answer = call("stdlib_api_search", "{\"term\":\"map\"}");

        assertFalse(answer.get("isError").asBoolean());
        assertTrue(text(answer).contains("List.map"), text(answer));
    }

    @Test
    void everyToolSaysWhatArgumentsItHasSoNoneHaveToBeGuessed() {
        JsonNode tools = serve("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/list\"}")
                .getFirst().get("result").get("tools");

        assertTrue(tools.valueStream().allMatch(
                        t -> !t.get("inputSchema").get("additionalProperties").asBoolean()),
                "the schema closes the set, so a client learns the arguments rather than trying them");
    }

    private String printed(String[] args) {
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        PrintStream stream = new PrintStream(captured, true, StandardCharsets.UTF_8);
        if (args.length > 0 && args[0].startsWith("--source")) {
            ApiCommand.run(args, stream, stream);
        } else {
            DocCommand.run(args, stream, stream);
        }
        return captured.toString(StandardCharsets.UTF_8);
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
