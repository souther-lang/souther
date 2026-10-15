package souther.lsp;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.lsp.Session.message;
import static souther.lsp.Session.publishedFor;

/**
 * A diagnose tells each open document what it says now, and says nothing to a document whose set
 * is the one the client already holds.
 *
 * <p>Every diagnose answers for every open document, because an edit to one module can change what
 * another reports. Most edits do not, and a set sent again is a frame the client reads, compares and
 * throws away, once for every open document at every pause in typing. What makes leaving it out
 * safe is that the client still holds the last one, and the one thing that takes it away is closing
 * the document — so a document opened again is told again, whatever it was told before.
 */
class WhatAClientAlreadyHoldsIsNotSentAgainTest {

    private static final String A = "file:///held/a.sou";

    private static final String B = "file:///held/b.sou";

    /** Two modules that read nothing of each other, so an edit to one leaves the other's set alone. */
    private static final String A_TEXT = "module a\ndata M = { name String }\n";   // missing `:`

    private static final String B_TEXT = "module b\ndata N = { v Int }\n";   // missing `:`

    @Test
    void anEditToOneDocumentSendsNothingToAnotherWhoseSetIsUnchanged() {
        try (Session session = new Session()) {
            session.send(handshake());
            session.send(opened(A, A_TEXT), opened(B, B_TEXT));
            session.await(publishedFor(A), "the diagnostics of a");
            session.await(publishedFor(B), "the diagnostics of b");
            session.awaitQuiet();
            long toA = session.count(publishedFor(A));
            long toB = session.count(publishedFor(B));

            session.send(message(null, "textDocument/didChange",
                    changedTo(B, "module b\ndata N = { v: Int }\n")));
            session.awaitAtLeast(toB + 1, publishedFor(B), "b's set, which the edit cleared");
            session.awaitQuiet();

            assertEquals(toA, session.count(publishedFor(A)),
                    "a says what it said before the edit, and the client holds that already");
        }
    }

    @Test
    void aDocumentOpenedAgainIsToldAgain() {
        try (Session session = new Session()) {
            session.send(handshake());
            session.send(opened(A, A_TEXT));
            session.await(publishedFor(A), "the diagnostics of a");
            session.awaitQuiet();
            long before = session.count(publishedFor(A));

            // Closing it clears what the client shows, which is a publish of its own.
            session.send(message(null, "textDocument/didClose",
                    Map.of("textDocument", Map.of("uri", A))));
            session.awaitAtLeast(before + 1, publishedFor(A), "the clearing of a");

            session.send(opened(A, A_TEXT));
            session.awaitAtLeast(before + 2, publishedFor(A),
                    "a's set again, which the client no longer holds");
        }
    }

    private static String[] handshake() {
        return new String[] {
            message(1, "initialize", Map.of()),
            message(null, "initialized", Map.of()),
        };
    }

    private static String opened(String uri, String text) {
        return message(null, "textDocument/didOpen",
                Map.of("textDocument", Map.of("uri", uri, "text", text)));
    }

    private static Map<String, Object> changedTo(String uri, String text) {
        Map<String, Object> params = new LinkedHashMap<>();
        params.put("textDocument", Map.of("uri", uri));
        params.put("contentChanges", List.of(Map.of("text", text)));
        return params;
    }
}
