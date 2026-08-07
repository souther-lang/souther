package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import tools.jackson.core.json.JsonReadFeature;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A document that tells its reader to go and read something else is telling it to whoever asked,
 * and the two askers do not ask the same way. Written as one operation and spelled at the point it
 * is read, the instruction stays followable on both wires.
 *
 * <p>What is checked here is that the spelling a reader is handed is one that reader can act on —
 * a client's is asked for over the protocol and has to be answered, not merely to look like a tool
 * call. Text about what a command is stays as it is written, because it is a true thing to say to
 * anyone.
 */
class ADocumentSendsItsReaderWhereThatReaderCanGoTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Reads an argument object spelled as a document writes one, property names unquoted. */
    private static final JsonMapper AS_WRITTEN = JsonMapper.builder()
            .enable(JsonReadFeature.ALLOW_UNQUOTED_PROPERTY_NAMES)
            .build();

    /** An argument standing for one the reader supplies, which is not a call to make. */
    private static final Pattern STANDS_IN = Pattern.compile("<[^>]+>");

    @Test
    void theSameInstructionIsSpelledForWhoeverIsReadingIt() {
        String atAPrompt = read("cli/start-here", Caller.CLI);
        String overTheProtocol = read("cli/start-here", Caller.MCP);

        assertTrue(atAPrompt.contains("`souther doc example`"), atAPrompt);
        assertTrue(overTheProtocol.contains("`doc_read {name: \"example\"}`"), overTheProtocol);
        assertNotEquals(atAPrompt, overTheProtocol);
    }

    @Test
    void theDocumentAReaderStartsAtOffersNoCommandItCannotRun() {
        String overTheProtocol = read("cli/start-here", Caller.MCP);

        assertFalse(overTheProtocol.contains("souther doc"), overTheProtocol);
        assertFalse(overTheProtocol.contains("souther api"), overTheProtocol);
    }

    @Test
    void everyOperationTheShippedDocumentsOfferAClientIsOneTheServerAnswers() {
        List<String> offered = new ArrayList<>();
        for (String tool : published()) {
            // Named against the published table rather than by shape, because a code span of a
            // record literal is written the same way and is not an offer to call anything.
            Pattern call = Pattern.compile("`(" + tool + ") (\\{[^`]*})`");
            for (LibraryDocs.Topic topic : LibraryDocs.on(loader(), Caller.MCP).topics()) {
                Matcher offer = call.matcher(read(topic.name(), Caller.MCP));
                while (offer.find()) {
                    if (!STANDS_IN.matcher(offer.group(2)).find()) {
                        offered.add(offer.group(1) + " " + offer.group(2));
                    }
                }
            }
        }

        assertFalse(offered.isEmpty(), "there are offers to check, so this is not passing on silence");
        for (String call : offered) {
            int space = call.indexOf(' ');
            JsonNode answer = called(call.substring(0, space), call.substring(space + 1));
            assertFalse(answer.has("error"), call + " → " + answer);
            assertFalse(answer.get("result").get("isError").asBoolean(),
                    call + " → " + answer.get("result").get("content").get(0).get("text").asString());
        }
    }

    @Test
    void aSearchAnswersOverTheWordsItsOwnReaderIsShown() {
        assertTrue(found("doc_read", Caller.MCP).contains("cli/start-here"),
                "the client's own spelling is in the text the client is ranked against");
        assertFalse(found("doc_read", Caller.CLI).contains("cli/start-here"),
                "and a reader at a prompt is not ranked against a spelling it was never shown");

        assertTrue(found("souther doc", Caller.CLI).contains("cli/start-here"),
                "the same instruction, found by the spelling that reader was shown");
        assertFalse(found("souther doc", Caller.MCP).contains("cli/start-here"),
                "ranking the source rather than the answer would hand this reader, in the snippet,"
                        + " the operation the document was read not to offer");
    }

    /** The names of the topics a search for {@code term} answers {@code caller} with. */
    private List<String> found(String term, Caller caller) {
        ByteArrayOutputStream answered = new ByteArrayOutputStream();
        DocCommand.run(new String[]{"--search", term, "--limit", "0"},
                print(answered), print(answered), caller);
        return answered.toString(StandardCharsets.UTF_8).lines()
                .filter(line -> line.contains("\t"))
                .map(line -> line.substring(0, line.indexOf('\t')))
                .toList();
    }

    /** Every tool this server publishes, which is what an offer may name. */
    private List<String> published() {
        ByteArrayInputStream in = new ByteArrayInputStream(
                "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/list\"}\n".getBytes(StandardCharsets.UTF_8));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        McpServer.serve(in, out);
        List<String> names = new ArrayList<>();
        JSON.readTree(out.toString(StandardCharsets.UTF_8).strip())
                .get("result").get("tools").forEach(tool -> names.add(tool.get("name").asString()));
        return names;
    }

    @Test
    void anOperationNoCallerCanCarryOutIsRefusedWhereTheDocumentIsRead() {
        IllegalStateException unknown = assertThrows(IllegalStateException.class,
                () -> Affordance.materialize("Read {{souther-examples:order.sou}} next.", Caller.MCP));

        assertTrue(unknown.getMessage().contains("souther-examples"), unknown.getMessage());
    }

    @Test
    void anOperationWrittenWithoutWhatToAskForIsRefusedTheSameWay() {
        assertThrows(IllegalStateException.class,
                () -> Affordance.materialize("Read {{doc}} next.", Caller.MCP));
        assertThrows(IllegalStateException.class,
                () -> Affordance.materialize("Read {{stdlib:String}} next.", Caller.MCP));
    }

    @Test
    void anAnswerAndTheDocumentsAgreeOnHowToAskForAModulesSource() {
        ByteArrayOutputStream deferred = new ByteArrayOutputStream();
        ApiCommand.run(new String[]{"String.length"}, print(deferred), print(deferred), Caller.MCP);

        assertTrue(deferred.toString(StandardCharsets.UTF_8)
                        .contains(Affordance.STDLIB_SOURCE.spelled(Caller.MCP, "String")),
                "a command's own offer and a document's are one spelling, not two that drift:\n"
                        + deferred.toString(StandardCharsets.UTF_8));
    }

    private ClassLoader loader() {
        return ADocumentSendsItsReaderWhereThatReaderCanGoTest.class.getClassLoader();
    }

    private String read(String name, Caller caller) {
        return LibraryDocs.on(loader(), caller).read(name);
    }

    private PrintStream print(ByteArrayOutputStream to) {
        return new PrintStream(to, true, StandardCharsets.UTF_8);
    }

    /**
     * Makes the call a document offered, as written.
     *
     * <p>An offer is written to be read by whoever is reading the document, so its argument object
     * names its properties the way prose does. Reading it back here is lenient about that and
     * strict about everything else: what reaches the server is the operation and the arguments the
     * document named, and the server checks those against its own published schema.
     */
    private JsonNode called(String tool, String arguments) {
        String request = "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":{\"name\":\""
                + tool + "\",\"arguments\":" + JSON.writeValueAsString(AS_WRITTEN.readTree(arguments))
                + "}}";
        ByteArrayInputStream in = new ByteArrayInputStream(
                (request + "\n").getBytes(StandardCharsets.UTF_8));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        McpServer.serve(in, out);
        return JSON.readTree(out.toString(StandardCharsets.UTF_8).strip());
    }

    @Test
    void everySpellingADocumentOffersIsWrittenAsJsonTheServerReads() {
        assertEquals("`doc_read {name: \"example\"}`", Affordance.DOC.spelled(Caller.MCP, "example"));
        assertEquals("`souther doc example`", Affordance.DOC.spelled(Caller.CLI, "example"));
    }
}
