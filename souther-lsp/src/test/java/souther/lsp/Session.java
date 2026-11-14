package souther.lsp;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.test.WrittenOutput;

import java.io.IOException;
import java.io.PipedInputStream;
import java.io.PipedOutputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.BooleanSupplier;
import java.util.function.Predicate;

/**
 * A server running against a connection that stays open, for the tests about when it answers what.
 *
 * <p>The other protocol tests hand the server every frame at once and read what it wrote afterwards,
 * which is enough while the answer to a message depends only on the messages before it. It is not
 * enough here: what this server does with an idle moment is the thing being tested, and a stream
 * that is already at its end never has one. So the frames go in through a pipe the test holds open,
 * and the test waits on what comes back rather than on the session ending.
 */
final class Session implements AutoCloseable {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * What a hung server costs the build: the wait for a message that never comes ends here. It
     * decides nothing about a server that is slow, because a wait ends when the message is written
     * and this only bounds the case where it is not going to be.
     */
    private static final Duration HUNG = Duration.ofMinutes(2);

    private final PipedOutputStream toServer = new PipedOutputStream();

    /** The frames the server writes. */
    private final WrittenOutput fromServer = new WrittenOutput();

    private final Thread serving;

    private volatile Throwable stopped;

    private int nextBarrier = 1_000_000;

    Session() {
        PipedInputStream in;
        try {
            in = new PipedInputStream(toServer, 1 << 16);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        serving = Thread.ofPlatform().name("souther-lsp-under-test").start(() -> {
            try {
                LspServer.serve(in, fromServer);
            } catch (Throwable t) {
                stopped = t;
            } finally {
                fromServer.ended();
            }
        });
    }

    /** Writes the messages as one run of frames, the way a client that pipelines them would. */
    void send(String... messages) {
        try {
            for (String message : messages) {
                byte[] body = message.getBytes(StandardCharsets.UTF_8);
                toServer.write(("Content-Length: " + body.length + "\r\n\r\n")
                        .getBytes(StandardCharsets.US_ASCII));
                toServer.write(body);
            }
            toServer.flush();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /** Everything the server has written so far that can be read as a whole frame. */
    List<JsonNode> heard() {
        byte[] wrote = fromServer.bytes();
        List<JsonNode> messages = new ArrayList<>();
        int at = 0;
        while (true) {
            int blank = indexOf(wrote, at);
            if (blank < 0) {
                return messages;
            }
            String header = new String(wrote, at, blank - at, StandardCharsets.US_ASCII);
            int length = Integer.parseInt(header.substring(header.indexOf(':') + 1).trim());
            int body = blank + 4;
            if (body + length > wrote.length) {
                return messages;   // the frame is still being written
            }
            messages.add(JSON.readTree(new String(wrote, body, length, StandardCharsets.UTF_8)));
            at = body + length;
        }
    }

    /** How many of the messages written so far {@code what} holds of. */
    long count(Predicate<JsonNode> what) {
        return heard().stream().filter(what).count();
    }

    /** Waits for a message the server writes that {@code what} holds of, and answers with it. */
    JsonNode await(Predicate<JsonNode> what, String wanted) {
        JsonNode[] found = new JsonNode[1];
        awaitWritten(() -> {
            found[0] = heard().stream().filter(what).findFirst().orElse(null);
            return found[0] != null;
        }, wanted);
        return found[0];
    }

    /** Waits until the server has written at least {@code many} messages that {@code what} holds of. */
    void awaitAtLeast(long many, Predicate<JsonNode> what, String wanted) {
        awaitWritten(() -> count(what) >= many, wanted);
    }

    /**
     * Waits until the server has carried out everything sent before this call, and written what that
     * came to.
     *
     * <p>The server carries frames out in the order they arrive, so the reply to a request nothing
     * answers but an error is behind everything written for the frames before it: the replies, and
     * the diagnostics a diagnose that gave way to one of them had already published. What it does not
     * say is that the diagnose the last frame leaves owed has run.
     */
    void awaitCarriedOut() {
        int id = nextBarrier++;
        send(message(id, "souther/barrier", Map.of()));
        await(replyTo(id), "the reply to a request that only asks to be carried out in order");
    }

    private void awaitWritten(BooleanSupplier written, String wanted) {
        try {
            if (!fromServer.awaitUntil(written, HUNG)) {
                throw new AssertionError("the server never wrote " + wanted, stopped);
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }
    }

    @Override
    public void close() {
        try {
            toServer.close();
            serving.join(HUNG);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new AssertionError(e);
        }
        if (stopped != null) {
            throw new AssertionError("the session did not end the way a session ends", stopped);
        }
    }

    /** Where the blank line that ends a frame's header block begins, or -1 if it is not there yet. */
    private static int indexOf(byte[] wrote, int from) {
        for (int i = from; i + 3 < wrote.length; i++) {
            if (wrote[i] == '\r' && wrote[i + 1] == '\n' && wrote[i + 2] == '\r' && wrote[i + 3] == '\n') {
                return i;
            }
        }
        return -1;
    }

    /** One JSON-RPC message: a request when {@code id} is given, a notification when it is not. */
    static String message(Integer id, String method, Object params) {
        Map<String, Object> message = new LinkedHashMap<>();
        message.put("jsonrpc", "2.0");
        if (id != null) {
            message.put("id", id);
        }
        message.put("method", method);
        message.put("params", params);
        return JSON.writeValueAsString(message);
    }

    /** Whether {@code message} is the reply to the request numbered {@code id}. */
    static Predicate<JsonNode> replyTo(int id) {
        return m -> m.has("id") && !m.has("method") && m.get("id").asInt() == id;
    }

    /** Whether {@code message} publishes diagnostics for {@code uri}. */
    static Predicate<JsonNode> publishedFor(String uri) {
        return m -> m.has("method")
                && m.get("method").asString().equals("textDocument/publishDiagnostics")
                && m.get("params").get("uri").asString().equals(uri);
    }
}
