package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.io.IOException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.Enumeration;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A session reads the documents it answers from once.
 *
 * <p>The specification is 486KB of AsciiDoc and the shipped doc sets are every file on the class
 * path under their index, and reading them is what answering costs. A server that reads them for
 * each question it is asked pays that for each question: the documents cannot have moved, because a
 * bundled resource and a class path do not move while a process runs.
 *
 * <p>What is held to is the reading rather than the time it takes. A count is what a regression
 * here looks like — the set built where a request is served rather than where a session is — and it
 * says so whatever the machine it runs on. A duration would have to be given a threshold, and a
 * threshold loose enough not to fail on a slow machine is loose enough to pass on a server that
 * reads the specification for every question.
 */
class ASessionReadsItsDocumentsOnceTest {

    /**
     * A loader that counts what is asked of it, over the one the tests run under.
     *
     * <p>{@code getResources} is what a doc set is found by, so it is the reading this counts.
     * Everything else is passed through, this being a loader the documents are actually read from
     * rather than one standing in for it.
     */
    private static final class Counting extends ClassLoader {

        private final AtomicInteger asked = new AtomicInteger();

        private Counting(ClassLoader parent) {
            super(parent);
        }

        @Override
        public Enumeration<URL> getResources(String name) throws IOException {
            asked.incrementAndGet();
            return super.getResources(name);
        }
    }

    private static String reads(int n) {
        StringBuilder b = new StringBuilder();
        for (int i = 0; i < n; i++) {
            b.append("{\"jsonrpc\":\"2.0\",\"id\":").append(i + 1)
                    .append(",\"method\":\"tools/call\",\"params\":{\"name\":\"doc_read\","
                            + "\"arguments\":{\"name\":\"purpose\"}}}\n");
        }
        return b.toString();
    }

    private static int answered(String responses) {
        return responses.strip().isEmpty() ? 0 : responses.strip().split("\n").length;
    }

    @Test
    void howeverManyQuestionsItIsAsked() {
        Counting loader = new Counting(ASessionReadsItsDocumentsOnceTest.class.getClassLoader());
        ByteArrayOutputStream out = new ByteArrayOutputStream();

        McpServer.serve(new ByteArrayInputStream(reads(20).getBytes(StandardCharsets.UTF_8)),
                out, loader);

        assertEquals(20, answered(out.toString(StandardCharsets.UTF_8)),
                "the session answered every question, so this is not counting a session that stopped");
        assertEquals(1, loader.asked.get(),
                "the doc sets were looked for once per question rather than once per session");
    }

    @Test
    void andOneQuestionCostsOneReadingToo() {
        Counting loader = new Counting(ASessionReadsItsDocumentsOnceTest.class.getClassLoader());
        ByteArrayOutputStream out = new ByteArrayOutputStream();

        McpServer.serve(new ByteArrayInputStream(reads(1).getBytes(StandardCharsets.UTF_8)),
                out, loader);

        assertEquals(1, answered(out.toString(StandardCharsets.UTF_8)));
        assertEquals(1, loader.asked.get(),
                "and a session of one is the same session, not a special case");
    }

    private static String printed(String[] args, Documents documents) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream stream = new PrintStream(out, true, StandardCharsets.UTF_8);
        assertEquals(0, DocCommand.run(args, stream, stream, documents));
        return out.toString(StandardCharsets.UTF_8);
    }

    /**
     * A command handed no documents reads them itself, and answers what it answers when it is
     * handed some. A one-shot invocation is still one, and which of the two read the documents is
     * where they came from rather than what they say.
     */
    @Test
    void aCommandWithNoDocumentsOfItsOwnReadsThemItselfAndSaysTheSame() {
        Counting loader = new Counting(ASessionReadsItsDocumentsOnceTest.class.getClassLoader());
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream stream = new PrintStream(out, true, StandardCharsets.UTF_8);

        int code = DocCommand.run(new String[]{"purpose"}, stream, stream, Caller.CLI, loader);

        assertEquals(0, code);
        assertTrue(out.size() > 0, "there is an answer to compare");
        assertEquals(printed(new String[]{"purpose"}, Documents.on(Caller.CLI, loader)),
                out.toString(StandardCharsets.UTF_8),
                "the answer is the same whether the documents were handed over or read here");
        assertEquals(2, loader.asked.get(), "one reading each, and no more");
    }
}
