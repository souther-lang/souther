package souther.compiler.doc;

import org.junit.jupiter.api.Test;
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
class ALongAnswerArrivesInPartsThatJoinBackUpTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** What a part that is not the last one ends with, and the cursor that carries it on. */
    private static final Pattern CARRIES_ON = Pattern.compile(
            "(?s)^(.*)\n… (\\d+) more characters; `doc_read (\\{.*?})` for what follows\n$");

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
    void noPartIsLargerThanTheOneAnswerAnyOtherToolGivesWhole() {
        for (String part : every(LONG)) {
            assertTrue(part.length() <= 16_000, "a part of " + part.length() + " characters");
        }
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
        String fenced = "= A section\n\n" + "x".repeat(200) + "\n\n```\n"
                + ("a line inside the block\n\n".repeat(2_000)) + "```\nafter the block\n";

        Continuation.Part first = Continuation.of(fenced, null);
        Continuation.Part second = Continuation.of(fenced, first.cursor());

        assertTrue(first.text().endsWith("x\n"),
                "cut before the blank line that is the last one outside the block");
        assertFalse(first.text().contains("a line inside the block"),
                "the blank lines inside it are content, and the count ran out well past them");
        assertTrue(second.text().startsWith("\n```\n"), "and the block itself is still whole");
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
        String elsewhere = JSON.readTree(first.group(3).replace("name:", "\"name\":")
                .replace("cursor:", "\"cursor\":")).get("cursor").asString();

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
        while (true) {
            String said = text(call(arguments));
            Matcher carriesOn = CARRIES_ON.matcher(said);
            if (!carriesOn.matches()) {
                parts.add(said);
                return parts;
            }
            parts.add(carriesOn.group(1));
            assertEquals(Integer.parseInt(carriesOn.group(2)),
                    printed(name).length() - String.join("", parts).length(),
                    "a part says how much of the document is still to come");
            arguments = carriesOn.group(3).replace("name:", "\"name\":")
                    .replace("cursor:", "\"cursor\":");
            assertTrue(parts.size() < 100, "the walk is not advancing");
        }
    }

    private String printed(String name) {
        ByteArrayOutputStream captured = new ByteArrayOutputStream();
        PrintStream stream = new PrintStream(captured, true, StandardCharsets.UTF_8);
        DocCommand.run(new String[]{name}, stream, stream, Caller.MCP);
        return captured.toString(StandardCharsets.UTF_8);
    }

    private String text(JsonNode result) {
        return result.get("content").get(0).get("text").asString();
    }

    private JsonNode call(String arguments) {
        return called(arguments).get("result");
    }

    private JsonNode called(String arguments) {
        ByteArrayInputStream in = new ByteArrayInputStream(
                ("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"tools/call\",\"params\":{\"name\":"
                        + "\"doc_read\",\"arguments\":" + arguments + "}}\n")
                        .getBytes(StandardCharsets.UTF_8));
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        McpServer.serve(in, out);
        return JSON.readTree(out.toString(StandardCharsets.UTF_8).strip());
    }

    @Test
    void everyLongAnswerThereIsJoinsBackUp() {
        ByteArrayOutputStream listed = new ByteArrayOutputStream();
        DocCommand.run(new String[]{}, new PrintStream(listed, true, StandardCharsets.UTF_8),
                new PrintStream(listed, true, StandardCharsets.UTF_8), Caller.MCP);

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
