package souther.compiler.doc;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.Timeout;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;
import tools.jackson.databind.node.ObjectNode;

import javax.tools.ToolProvider;
import java.io.BufferedReader;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.PrintStream;
import java.io.PrintWriter;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A client reads an answer too long for one part by making the same call again with each part's
 * cursor. The part is cut from the whole answer, and making the whole answer again for each part
 * would pay for all of it once per part — for {@code jar_api}, opening the jar and, where it has
 * sources, running the compiler's front end over them every time.
 *
 * <p>What shows that the tool was not run again is that it could not have answered: the jar is
 * gone by the time the second part is asked for. A server that ran the tool for it would say the
 * class is nowhere on the class path.
 *
 * <p>An answer kept is only the answer a cursor came from when the cursor says so. A cursor from
 * the answer the same call makes now is carried on from that answer, and a cursor from neither is
 * refused, as it is when nothing was kept.
 */
@Timeout(120)
class ThePartsOfALongAnswerAreCutFromTheAnswerAlreadyMadeTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final Pattern CARRIES_ON = Pattern.compile("(?s)^(.*)\n… (\\d+) more characters; ask"
            + " `jar_api` again with the same arguments and `cursor: \"([A-Za-z0-9_-]+)\"` for what follows\n$");

    /** A directory under the working directory, the only place a confined run reads. */
    private static Path underTheWorkingDirectory() throws IOException {
        return Files.createTempDirectory(Files.createDirectories(Path.of("target")), "long-answer")
                .toAbsolutePath();
    }

    /** A jar in {@code dir} whose one class has more members than one part carries, each named
     *  {@code member} and a number. */
    private static Path aJarWithALongAnswer(Path dir, String member) throws IOException {
        StringBuilder members = new StringBuilder();
        for (int i = 0; i < 800; i++) {
            members.append("    public void ").append(member).append(i).append("(int value) {}\n");
        }
        Path src = Files.createDirectories(dir.resolve("src/acme")).resolve("Many.java");
        Files.writeString(src, "package acme;\n\npublic final class Many {\n" + members + "}\n");
        Path compiled = Files.createDirectories(dir.resolve("compiled"));
        assertEquals(0, ToolProvider.getSystemJavaCompiler().run(null, OutputStream.nullOutputStream(),
                OutputStream.nullOutputStream(), "-proc:none", "-d", compiled.toString(), src.toString()));
        Path jar = dir.resolve("many-1.0.jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            out.putNextEntry(new JarEntry("acme/Many.class"));
            out.write(Files.readAllBytes(compiled.resolve("acme/Many.class")));
        }
        return jar;
    }

    /** What a prompt prints for the class, which is the whole of what the parts carry. */
    private static String printed(Path jar) {
        ByteArrayOutputStream printed = new ByteArrayOutputStream();
        PrintStream stream = new PrintStream(printed, true, StandardCharsets.UTF_8);
        assertEquals(0, JapiCommand.run(new String[]{"acme.Many", "-cp", jar.toString()}, stream, stream));
        return printed.toString(StandardCharsets.UTF_8);
    }

    /** One server, asked over its stdio one request after another. */
    private static final class Session implements AutoCloseable {

        private final PrintWriter requests;
        private final BufferedReader answers;
        private final Thread server;
        private int asked;

        Session() throws IOException {
            PipedOutputStream toServer = new PipedOutputStream();
            PipedInputStream serverReads = new PipedInputStream(toServer, 1 << 16);
            PipedInputStream fromServer = new PipedInputStream(1 << 20);
            PipedOutputStream serverWrites = new PipedOutputStream(fromServer);
            server = new Thread(() -> McpServer.serve(serverReads, serverWrites), "mcp-session");
            server.setDaemon(true);
            server.start();
            requests = new PrintWriter(new OutputStreamWriter(toServer, StandardCharsets.UTF_8), true);
            answers = new BufferedReader(new InputStreamReader(fromServer, StandardCharsets.UTF_8));
        }

        /** The result of {@code jar_api} for the class in {@code jar}, carried on from {@code cursor}. */
        JsonNode called(Path jar, String cursor) throws IOException {
            ObjectNode arguments = JSON.createObjectNode();
            arguments.put("name", "acme.Many");
            arguments.put("classpath", jar.toString());
            if (cursor != null) {
                arguments.put("cursor", cursor);
            }
            ObjectNode request = JSON.createObjectNode();
            request.put("jsonrpc", "2.0");
            request.put("id", ++asked);
            request.put("method", "tools/call");
            ObjectNode params = request.putObject("params");
            params.put("name", "jar_api");
            params.set("arguments", arguments);
            requests.println(JSON.writeValueAsString(request));
            return JSON.readTree(answers.readLine()).get("result");
        }

        @Override
        public void close() throws IOException {
            requests.close();   // the server's reader sees the end of the stream and the loop returns
            try {
                server.join(10_000);
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
            answers.close();
        }
    }

    private static String text(JsonNode result) {
        return result.get("content").get(0).get("text").asString();
    }

    @Test
    void theNextPartIsCutFromTheAnswerTheFirstPartCameFrom() throws Exception {
        Path jar = aJarWithALongAnswer(underTheWorkingDirectory(), "member");
        String whole = printed(jar);

        try (Session session = new Session()) {
            StringBuilder joined = new StringBuilder();
            int parts = 0;
            String cursor = null;
            while (true) {
                JsonNode result = session.called(jar, cursor);
                assertFalse(result.get("isError").asBoolean(), "part " + (parts + 1) + ": " + result);
                parts++;
                Matcher carriesOn = CARRIES_ON.matcher(text(result));
                if (!carriesOn.matches()) {
                    joined.append(text(result));
                    break;
                }
                joined.append(carriesOn.group(1));
                // Gone once the first part is in hand, so a part that arrives after this was not
                // made by running the tool again.
                Files.deleteIfExists(jar);
                cursor = carriesOn.group(3);
                assertTrue(parts < 100, "the walk is not advancing");
            }

            assertTrue(parts > 1, "the answer did not arrive whole, so there was a part to cut");
            assertEquals(whole, joined.toString(), "and the parts are the answer the first one came from");
        }
    }

    @Test
    void aCursorFromAnotherAnswerToTheSameCallIsHeldAgainstWhatTheCallAnswersNow() throws Exception {
        Path dir = underTheWorkingDirectory();
        Path jar = aJarWithALongAnswer(dir, "member");

        try (Session keeping = new Session(); Session another = new Session()) {
            Matcher before = CARRIES_ON.matcher(text(keeping.called(jar, null)));
            assertTrue(before.matches(), "the answer did not arrive whole, so it is kept for its parts");

            // The jar is rebuilt with other members, so the same call answers something else now,
            // and a cursor into that answer is taken from a session that never saw the first one.
            aJarWithALongAnswer(dir, "other");
            String now = printed(jar);
            Matcher elsewhere = CARRIES_ON.matcher(text(another.called(jar, null)));
            assertTrue(elsewhere.matches());

            JsonNode carriedOn = keeping.called(jar, elsewhere.group(3));
            assertFalse(carriedOn.get("isError").asBoolean(),
                    "a cursor from the answer this call makes now carries on from it: " + carriedOn);
            String second = text(carriedOn);
            Matcher secondCarriesOn = CARRIES_ON.matcher(second);
            String part = secondCarriesOn.matches() ? secondCarriesOn.group(1) : second;
            assertTrue(now.startsWith(elsewhere.group(1) + part),
                    "and what follows is the answer the cursor came from, not the one that was kept");

            JsonNode stale = keeping.called(jar, before.group(3));
            assertTrue(stale.get("isError").asBoolean(),
                    "a cursor from an answer the call no longer makes is refused: " + stale);
            assertTrue(text(stale).contains("ask again without one"), text(stale));
        }
    }
}
