package souther.compiler.doc;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStreamWriter;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Naming a smaller thing and handing over a smaller answer are different guarantees. Every
 * diagnostic the specification explains is asked for by its own code, and {@code compile-errors} is
 * still all of them at once, because a section's body runs on through its subsections. So a client
 * reading it needs the answer to arrive in parts.
 *
 * <p>What is checked here is that the parts are the document: followed to the end and put back
 * together they are, to the character, what the same read prints at a prompt. A reader that is
 * handed a document in pieces has been handed the document only if none of it was dropped between
 * them and none of it was said twice.
 */
@Timeout(120)
class ALongAnswerArrivesInPartsThatJoinBackUpTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * One session, held open for the whole of this class.
     *
     * <p>A client asks a long answer for its parts one after another, each request carrying the
     * cursor the last one answered with, and it asks them of a session it already has. Opening one
     * per request would be a client this protocol does not have, and would put the reading of the
     * documents — which is what answering costs — inside the walk being measured here.
     *
     * <p>Requests and responses are one for one and in order, so writing a line and reading a line
     * is the whole of the exchange.
     */
    private static PrintWriter SESSION;
    private static BufferedReader ANSWERS;
    private static Thread SERVER;

    /** How many requests this session has been sent, which is where a request's id comes from. */
    private static int asked;

    /**
     * The documents the checks that do not go through the protocol read, held for the same reason
     * the session is: what is under test is how an answer is cut, not what it costs to find one.
     */
    private static Documents DOCUMENTS;

    @BeforeAll
    static void openTheSession() throws IOException {
        DOCUMENTS = Documents.on(Caller.MCP,
                ALongAnswerArrivesInPartsThatJoinBackUpTest.class.getClassLoader());
        PipedOutputStream toServer = new PipedOutputStream();
        PipedInputStream serverReads = new PipedInputStream(toServer, 1 << 16);
        PipedInputStream fromServer = new PipedInputStream(1 << 20);
        PipedOutputStream serverWrites = new PipedOutputStream(fromServer);
        SESSION = new PrintWriter(new OutputStreamWriter(toServer, StandardCharsets.UTF_8), true);
        ANSWERS = new BufferedReader(new InputStreamReader(fromServer, StandardCharsets.UTF_8));
        SERVER = new Thread(() -> McpServer.serve(serverReads, serverWrites), "mcp-session");
        SERVER.setDaemon(true);
        SERVER.start();
    }

    @AfterAll
    static void closeTheSession() throws InterruptedException {
        SESSION.close();   // the server's reader sees the end of the stream and the loop returns
        SERVER.join(10_000);
    }

    /** What a part that is not the last one ends with, and the cursor that carries it on. */
    private static final Pattern CARRIES_ON = carriesOn("doc_read");

    /** The same, for whichever tool was asked. */
    private static Pattern carriesOn(String tool) {
        return Pattern.compile("(?s)^(.*)\n… (\\d+) more characters; ask `" + tool + "` again with"
                + " the same arguments and `cursor: \"([A-Za-z0-9_-]+)\"` for what follows\n$");
    }

    /** A name whose answer is the longest there is, and one whose answer is ordinary. */
    private static final String LONG = "compile-errors";
    private static final String SHORT = "purpose";

    @Test
    void thePartsOfALongAnswerAreTheWholeOfIt() {
        List<String> parts = every(LONG);

        assertTrue(parts.size() > 1, "the longest answer there is does not arrive whole");
        assertEquals(printed(LONG), String.join("", parts),
                "put back together, the parts are the document — nothing dropped between two of"
                        + " them and nothing said twice");
    }

    @Test
    void whatIsCountedIsTheWholeAnswerAndNotOnlyItsText() {
        // A search answers in lines, so nothing in it is a heading or a blank line and a part runs
        // right up to the count. That is where the room set aside for the line carrying it on is
        // either there or the answer is over.
        int parts = counted("doc_search", "{\"term\":\"a\",\"limit\":0}");

        assertTrue(parts > 1, "an answer of forty thousand characters does not arrive whole");
        assertTrue(counted("doc_read", "{\"name\":\"" + LONG + "\"}") > 1);
    }

    /** Follows a call to the end, holding every answer against the count. Answers how many. */
    private int counted(String tool, String base) {
        int parts = 0;
        String arguments = base;
        while (true) {
            String said = text(called(tool, arguments).get("result"));
            parts++;
            assertTrue(said.length() <= Continuation.MOST,
                    tool + " answered with " + said.length() + " characters — the line that carries"
                            + " a part on is part of the answer and comes out of the count");
            Matcher carriesOn = carriesOn(tool).matcher(said);
            if (!carriesOn.matches()) {
                return parts;
            }
            arguments = withCursor(base, carriesOn.group(3));
            assertTrue(parts < 100, "the walk is not advancing");
        }
    }

    /** The call that was made, made again with the cursor that carries it on. */
    private String withCursor(String arguments, String cursor) {
        return arguments.substring(0, arguments.length() - 1)
                + (arguments.length() > 2 ? "," : "") + "\"cursor\":\"" + cursor + "\"}";
    }

    @Test
    void aCallerCannotWriteItsOwnArgumentsIntoAnAnswerAndPushItPastTheCount() {
        // The caller's arguments are the caller's, and there is no length a schema can name that
        // makes them safe to put inside an answer this server is promising to bound. What carries
        // an answer on names only what this server issued.
        int parts = counted("doc_search", "{\"term\":\"" + "x".repeat(20_000) + "\",\"limit\":0}");

        assertTrue(parts > 1, "a term longer than the count is answered in parts like anything else");
    }

    @Test
    void aLineLongerThanAnAnswerCarriesIsCutWhereTheCountRunsOut() {
        String oneLine = "x".repeat(20_000) + "\n";

        List<String> parts = everyPartOf(oneLine);

        assertEquals(oneLine, String.join("", parts));
        parts.forEach(part -> assertTrue(part.length() <= Continuation.MOST,
                "a part of " + part.length() + " characters: a line nothing can be cut at is still"
                        + " cut, or the count is not a count"));
    }

    @Test
    void aBlockLongerThanAnAnswerCarriesIsCutRatherThanKeptWhole() {
        String oneBlock = "# T\n\n```\n" + "y".repeat(20_000) + "\n```\nafter\n";

        List<String> parts = everyPartOf(oneBlock);

        assertEquals(oneBlock, String.join("", parts));
        parts.forEach(part -> assertTrue(part.length() <= Continuation.MOST, part.length() + ""));
        assertTrue(parts.size() <= 4, "and it is not handed over a few characters at a time: "
                + parts.stream().map(String::length).toList());
    }

    /** Every part {@link Continuation} cuts {@code text} into, followed to the end. */
    private List<String> everyPartOf(String text) {
        List<String> parts = new ArrayList<>();
        String cursor = null;
        do {
            Continuation.Part part = Continuation.of(text, cursor, Continuation.MOST);
            parts.add(part.text());
            cursor = part.cursor();
            assertTrue(parts.size() < 100, "the walk is not advancing");
        } while (cursor != null);
        return parts;
    }

    @Test
    void aPartStopsWhereTheDocumentSaysToAndNotWhereTheCountRanOut() {
        List<String> parts = every(LONG);

        for (int at = 1; at < parts.size(); at++) {
            String opens = parts.get(at).lines().findFirst().orElse("");
            assertTrue(opens.startsWith("[") || opens.startsWith("=") || opens.isBlank(),
                    "part " + (at + 1) + " opens mid-paragraph: " + opens);
        }
        assertTrue(parts.get(1).startsWith("[#"),
                "and where a heading was in reach it stopped before the names that heading is"
                        + " asked for by, not after them: " + parts.get(1).lines().findFirst().orElse(""));
    }

    /** The delimiters that open and close a block whose text is taken as it stands. */
    private static final Pattern DELIMITER = Pattern.compile("^(```|~~~).*$|^([-.+/])\\2{3,}$");

    @Test
    void noPartEndsInsideABlockTakenAsItStands() {
        int checked = 0;
        for (String name : List.of(LONG, "raoh/tutorial", "stdlib", "fn")) {
            for (String part : every(name)) {
                assertEquals(0, part.lines().filter(line -> DELIMITER.matcher(line.strip()).matches())
                                .count() % 2,
                        name + ": a part opens a block taken as it stands and does not close it");
                checked++;
            }
        }
        assertTrue(checked > 8, "only " + checked + " parts, so this is not passing on silence");
    }

    @Test
    void aBlankLineInsideSuchABlockIsContentAndNotAPlaceToStop() {
        // A block that fits in one answer, with the last blank line before the count runs out
        // inside it. Taking that one would cut a fence in half for no reason: there is a blank
        // line outside the block that leaves the whole of it for the part after.
        String prose = "a paragraph outside the block\n\n".repeat(330);
        String block = "```\n" + "a line inside the block\n\n".repeat(190) + "```\n";
        String fenced = prose + block + "z".repeat(6_000) + "\n";

        Continuation.Part first = Continuation.of(fenced, null, Continuation.MOST);

        assertTrue(prose.length() > 9_000 && prose.length() + block.length() < 16_000,
                "the block fits, and the last blank line in reach is inside it: "
                        + prose.length() + " then " + block.length());
        assertFalse(first.text().contains("```"),
                "the part stopped at a blank line outside the block, leaving the block whole:\n"
                        + first.text().substring(Math.max(0, first.text().length() - 120)));
        assertTrue(Continuation.of(fenced, first.cursor(), Continuation.MOST).text().contains(block),
                "and the block arrives in one piece");
    }

    @Test
    void anAnswerThatFitsArrivesWholeWithNothingToCarryOn() {
        String only = text(call("{\"name\":\"" + SHORT + "\"}"));

        assertEquals(printed(SHORT), only);
        assertNull(CARRIES_ON.matcher(only).matches() ? "carried on" : null,
                "an answer inside the count is not cut, and offers no cursor to a client that"
                        + " would then spend a call on it");
    }

    @Test
    void aCursorMeasuredAgainstAnotherAnswerIsRefusedRatherThanResumedAt() {
        Matcher first = CARRIES_ON.matcher(text(call("{\"name\":\"" + LONG + "\"}")));
        assertTrue(first.matches());
        String elsewhere = first.group(3);

        JsonNode answer = called("{\"name\":\"stdlib\",\"cursor\":\"" + elsewhere + "\"}");

        assertTrue(answer.get("result").get("isError").asBoolean(),
                "resuming here would answer from the middle of a document nobody asked about");
        assertTrue(text(answer.get("result")).contains("ask again without one"),
                text(answer.get("result")));
    }

    @Test
    void aValueThatWasNeverACursorIsRefusedAgainstTheSchema() {
        JsonNode answer = called("{\"name\":\"" + LONG + "\",\"cursor\":\"not a cursor\"}");

        assertEquals(-32602, answer.get("error").get("code").asInt(), answer.toString());
    }

    @Test
    void aReaderAtAPromptIsNotCutAtAll() {
        assertTrue(printed(LONG).length() > 60_000,
                "how much a caller is handed at once is the transport's question, and a terminal"
                        + " has its own answer to it");
    }

    /** Every part of {@code name}, in order, with the line that carries each one on removed. */
    private List<String> every(String name) {
        List<String> parts = new ArrayList<>();
        String arguments = "{\"name\":\"" + name + "\"}";
        int printed = -1;
        while (true) {
            String said = text(call(arguments));
            Matcher carriesOn = CARRIES_ON.matcher(said);
            if (!carriesOn.matches()) {
                parts.add(said);
                return parts;
            }
            parts.add(carriesOn.group(1));
            if (printed < 0) {
                printed = printed(name).length();
            }
            assertEquals(Integer.parseInt(carriesOn.group(2)),
                    printed - String.join("", parts).length(),
                    "a part says how much of the document is still to come");
            arguments = withCursor("{\"name\":\"" + name + "\"}", carriesOn.group(3));
            assertTrue(parts.size() < 100, "the walk is not advancing");
        }
    }

    private String printed(String name) {
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        PrintStream stream = new PrintStream(captured, true, StandardCharsets.UTF_8);
        DocCommand.run(new String[]{name}, stream, stream, DOCUMENTS);
        return captured.toString(StandardCharsets.UTF_8);
    }

    private String text(JsonNode result) {
        return result.get("content").get(0).get("text").asString();
    }

    private JsonNode call(String arguments) {
        return called(arguments).get("result");
    }

    private JsonNode called(String arguments) {
        return called("doc_read", arguments);
    }

    private JsonNode called(String tool, String arguments) {
        SESSION.println("{\"jsonrpc\":\"2.0\",\"id\":" + (++asked)
                + ",\"method\":\"tools/call\",\"params\":{\"name\":\""
                + tool + "\",\"arguments\":" + arguments + "}}");
        try {
            String answered = ANSWERS.readLine();
            assertNotNull(answered, "the session ended before it answered");
            return JSON.readTree(answered);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Test
    void everyLongAnswerThereIsJoinsBackUp() {
        ByteArrayOutputStream listed = new ByteArrayOutputStream();
        DocCommand.run(new String[]{}, new PrintStream(listed, true, StandardCharsets.UTF_8),
                new PrintStream(listed, true, StandardCharsets.UTF_8), DOCUMENTS);

        List<String> cut = new ArrayList<>();
        for (String line : listed.toString(StandardCharsets.UTF_8).split("\n")) {
            String name = line.substring(0, line.indexOf('\t'));
            List<String> parts = every(name);
            if (parts.size() > 1) {
                cut.add(name);
                assertEquals(printed(name), String.join("", parts), name);
            }
        }
        assertFalse(cut.isEmpty(), "there are answers being cut, so this is not passing on silence");
    }
}
