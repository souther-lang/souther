package souther.lsp;

import org.junit.jupiter.api.Test;
import souther.lsp.analysis.Analyzer;
import souther.lsp.transport.MessageConnection;
import tools.jackson.databind.json.JsonMapper;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.nio.charset.StandardCharsets;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A document the compiler cannot walk must not take the server with it. Analysis catches
 * {@code RuntimeException} so the session survives a compiler bug, but a {@code StackOverflowError}
 * is an {@code Error}: before this was handled, opening a deeply nested expression unwound the
 * dispatch loop and the editor's language server simply exited.
 *
 * <p>Both cases run on a thread with a small, fixed stack, so "too deep" means the same thing on
 * every machine — otherwise the document compiles cleanly on a roomier stack and the test passes
 * without having exercised anything.
 */
class LspSurvivesADeepExpressionTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String DEEP = """
            module m

            data N = Int

            behavior f : (n: N) -> N constructs N
            let f (n) = N { value = %s }
            """.formatted("(".repeat(5000) + "1" + ")".repeat(5000));

    /** Small enough that DEEP is past it on any platform. */
    private static final int STACK_BYTES = 256 * 1024;

    @Test
    void analysisReportsRatherThanThrows() throws InterruptedException {
        AtomicReference<Object> result = new AtomicReference<>();
        onSmallStack(() -> result.set(new Analyzer().diagnostics(DEEP)));

        assertTrue(result.get() instanceof java.util.List<?> l && !l.isEmpty(),
                "a document the compiler cannot walk should be marked, not silently accepted;"
                        + " got " + result.get());
    }

    @Test
    void theSessionOutlivesTheDocument() throws InterruptedException {
        byte[] input = frames(
                message(1, "initialize", Map.of()),
                message(null, "initialized", Map.of()),
                message(null, "textDocument/didOpen", Map.of("textDocument",
                        Map.of("uri", "file:///deep.sou", "text", DEEP))),
                message(2, "shutdown", Map.of()));

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        onSmallStack(() -> new LspServer(new MessageConnection(
                new ByteArrayInputStream(input), out)).run());

        assertTrue(out.toString(StandardCharsets.UTF_8).contains("\"id\":2"),
                "the server stopped reading before the request that followed the deep document");
    }

    /** Runs {@code work} on a thread with {@link #STACK_BYTES} of stack, rethrowing nothing: what is
     *  under test is what the code did with the failure, not that one happened. */
    private static void onSmallStack(Runnable work) throws InterruptedException {
        Thread t = new Thread(null, () -> {
            try {
                work.run();
            } catch (Throwable _) {
                // the assertions read what was produced, and a throw leaves that empty
            }
        }, "deep-expression", STACK_BYTES);
        t.start();
        t.join();
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
        StringBuilder sb = new StringBuilder();
        for (String m : messages) {
            byte[] body = m.getBytes(StandardCharsets.UTF_8);
            sb.append("Content-Length: ").append(body.length).append("\r\n\r\n").append(m);
        }
        return sb.toString().getBytes(StandardCharsets.UTF_8);
    }
}
