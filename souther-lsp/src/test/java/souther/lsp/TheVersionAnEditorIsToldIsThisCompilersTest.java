package souther.lsp;

import souther.compiler.meta.ModuleMetadata;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the handshake calls this server's version is the version this compiler reads of itself.
 *
 * <p>It was a literal, written once and left where it was written, so an editor was being told a
 * version this server is not. Which Souther this is has one answer, and the command line and the
 * handshake are two readers of it rather than two statements of it.
 */
class TheVersionAnEditorIsToldIsThisCompilersTest {

    @Test
    void theHandshakeStatesWhatTheCompilerReadsOfItself() {
        try (Session session = new Session()) {
            session.send(Session.message(1, "initialize", Map.of()));

            JsonNode answer = session.await(Session.replyTo(1), "an answer to initialize");

            assertEquals(ModuleMetadata.compilerVersion(),
                    answer.get("result").get("serverInfo").get("version").asString());
        }
    }
}
