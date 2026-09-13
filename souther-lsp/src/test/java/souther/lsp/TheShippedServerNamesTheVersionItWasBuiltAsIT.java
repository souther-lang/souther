package souther.lsp;

import souther.lsp.transport.MessageConnection;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The uber jar an editor launches states the version this build says it is.
 *
 * <p>The unit tests run from class files, where there is no manifest and the answer is
 * {@code unreleased}; they hold the handshake to the reading and cannot see whether the reading has
 * anything to read. What carries it is the manifest, and whether the manifest reaches this artifact
 * is decided by this module's own shade — a different one from the command line's, so the command
 * line's answer says nothing about this one.
 *
 * <p>That is the whole of what {@code souther-lsp-all.jar} is for: an editor bundles it and launches
 * it, and what it says about itself is what a reader of that editor sees. A shade that dropped the
 * attribute would tell every editor it is a build tree, and nothing else here would notice.
 */
class TheShippedServerNamesTheVersionItWasBuiltAsIT {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static Path jar;

    @BeforeAll
    static void theBuiltJar() {
        jar = Path.of(System.getProperty("souther.lsp.jar", "target/souther-lsp-all.jar"));
        assertTrue(Files.isRegularFile(jar),
                "the uber jar is built before this runs: " + jar.toAbsolutePath());
    }

    @Test
    void theHandshakeFromTheUberJarStatesWhatThisBuildIs() throws Exception {
        // Launched the way the editors are told to launch it, stack flag included.
        Process process = new ProcessBuilder(
                Path.of(System.getProperty("java.home"), "bin", "java").toString(),
                "-Xss4m", "-jar", jar.toString()).start();
        MessageConnection answers = new MessageConnection(
                process.getInputStream(), OutputStream.nullOutputStream());
        process.getOutputStream().write(frames(
                message(1, "initialize", Map.of()),
                message(null, "initialized", Map.of()),
                message(2, "shutdown", Map.of()),
                message(null, "exit", Map.of())));
        process.getOutputStream().close();

        JsonNode handshake = null;
        String frame;
        while (handshake == null && (frame = answers.read()) != null) {
            JsonNode m = JSON.readTree(frame);
            if (m.has("id") && m.get("id").isNumber() && m.get("id").asInt() == 1) {
                handshake = m;
            }
        }
        String said = new String(process.getErrorStream().readAllBytes(), StandardCharsets.UTF_8);
        assertEquals(0, process.waitFor(), "a client that shut the server down leaves it zero: " + said);

        assertNotNull(handshake, "the handshake was answered: " + said);
        assertEquals(System.getProperty("souther.version"),
                handshake.get("result").get("serverInfo").get("version").asString(),
                "the artifact an editor launches names the version this build is");
    }

    private static String message(Integer id, String method, Object params) {
        Map<String, Object> m = new LinkedHashMap<>();
        m.put("jsonrpc", "2.0");
        if (id != null) {
            m.put("id", id);
        }
        m.put("method", method);
        m.put("params", params);
        return JSON.writeValueAsString(m);
    }

    private static byte[] frames(String... messages) {
        ByteArrayOutputStream buffer = new ByteArrayOutputStream();
        MessageConnection writer =
                new MessageConnection(new ByteArrayInputStream(new byte[0]), buffer);
        for (String m : messages) {
            writer.write(m);
        }
        return buffer.toByteArray();
    }
}
