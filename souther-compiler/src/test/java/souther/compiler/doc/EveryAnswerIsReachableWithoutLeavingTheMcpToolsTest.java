package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

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
 *
 * <p>The two differ in how an operation is asked for and in nothing else. Which documents there
 * are, and which names a listing gives, are the same over both wires: a caller that cannot invoke
 * a command still gets the manual for it, with whatever that manual sends the reader to spelled as
 * a call this caller can make. A name held back from one listing would be a hole in the only map a
 * client has, and a name it cannot see is content that does not exist for it.
 */
class EveryAnswerIsReachableWithoutLeavingTheMcpToolsTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** A document sending a client to one name: {@code `doc_read {name: "sum-discrimination"}`}. */
    private static final Pattern SENT_TO = Pattern.compile("`doc_read \\{name: \"([^\"]+)\"}`");

    /** An argument standing for one the reader supplies, which is not a name to look for. */
    private static final Pattern STANDS_IN = Pattern.compile("<[^>]+>");

    /**
     * The listing is every section of the specification and every topic the shipped sets carry,
     * which is what a client is told it is. Held against those rather than against the other
     * caller's listing: two listings agreeing is not either of them being whole, and a name this
     * one holds and does not print is a name only a reader who already knew it can ask for.
     *
     * <p>That the sets themselves hold what their indexes promise is a separate guarantee, kept
     * where a doc set's own contract is.
     */
    @Test
    void aClientThatKnowsNoNameIsGivenEveryNameThereIs() {
        Set<String> listed = names(text(call("doc_read", "{}")));

        Set<String> thereIs = new TreeSet<>();
        SpecDocument.bundled(Caller.MCP).sections()
                .forEach(section -> thereIs.add(DocName.canonical(section.anchor())));
        LibraryDocs.on(getClass().getClassLoader(), Caller.MCP).topics()
                .forEach(topic -> thereIs.add(DocName.canonical(topic.name())));

        assertTrue(thereIs.size() > 300, "every section and every shipped topic, not a page of them");
        assertEquals(Set.of(), missing(thereIs, listed),
                "these are answered by name and the listing that names what there is does not give them");
        assertEquals(Set.of(), missing(listed, thereIs),
                "and the listing gives these, which nothing here is");
        assertTrue(listed.contains("cli/start-here"),
                "including the topic written for a reader who has never written Souther");
    }

    /**
     * A caller is answered in its own spelling, and a document's title is spelled as its text is,
     * so what the two listings have to agree on is which names they give rather than how each line
     * reads. Which documents there are is not something a wire decides.
     */
    @Test
    void aClientAndAReaderAtAPromptAreGivenTheSameNames() {
        assertEquals(names(printed(new String[]{})), names(text(call("doc_read", "{}"))));
    }

    /**
     * A client that starts at the listing and follows what it reads has to stay inside the set the
     * listing named. A document pointing out of it is an answer reachable only by a reader who was
     * already holding the document that points there, which is not the reader this listing is for.
     */
    @Test
    void everyNameADocumentSendsThisClientToIsOnTheListingItStartedFrom() {
        Set<String> listed = names(text(call("doc_read", "{}")));

        Set<String> sentTo = new TreeSet<>();
        LibraryDocs docs = LibraryDocs.on(getClass().getClassLoader(), Caller.MCP);
        docs.topics().forEach(topic -> namesIn(docs.read(topic.name()), sentTo));
        SpecDocument.bundled(Caller.MCP).sections()
                .forEach(section -> namesIn(section.body(), sentTo));

        assertFalse(sentTo.isEmpty(), "there are names to follow, so this is not passing on silence");
        assertEquals(Set.of(),
                sentTo.stream().filter(name -> !listed.contains(DocName.canonical(name)))
                        .collect(Collectors.toCollection(TreeSet::new)),
                "a document sends this client to these and the listing it starts from does not name them");
    }

    /** What {@code asked} holds and {@code given} does not, which is what a failure has to say. */
    private Set<String> missing(Set<String> asked, Set<String> given) {
        return asked.stream().filter(name -> !given.contains(name))
                .collect(Collectors.toCollection(TreeSet::new));
    }

    /** The names {@code text} sends a client to, leaving out one standing in for a name it supplies. */
    private void namesIn(String text, Set<String> found) {
        Matcher sent = SENT_TO.matcher(text);
        while (sent.find()) {
            if (!STANDS_IN.matcher(sent.group(1)).find()) {
                found.add(sent.group(1));
            }
        }
    }

    /** The names a listing gives, each as the lookup itself reads it. */
    private Set<String> names(String listing) {
        return listing.lines()
                .map(line -> DocName.canonical(line.substring(0, line.indexOf('\t'))))
                .collect(Collectors.toCollection(TreeSet::new));
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
        String three = text(call("doc_search", "{\"term\":\"type\",\"limit\":3}"));

        assertEquals(3, three.lines().filter(line -> line.contains("\t")).count(),
                "three hits, whatever the default would have been");
    }

    @Test
    void aModulesOwnSourceIsAToolCallAway() {
        String source = text(call("stdlib_api_source", "{\"name\":\"String\"}"));

        assertEquals(printed(new String[]{"--source", "String"}), source);
        assertTrue(source.contains("String."), "the module's own declarations, not its signatures alone");
    }

    @Test
    void theStdlibCanBeSearchedAndNotOnlyListedOrNamed() {
        JsonNode answer = call("stdlib_api_search", "{\"term\":\"map\"}");

        assertFalse(answer.get("isError").asBoolean());
        assertTrue(text(answer).contains("List.map"), text(answer));
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
