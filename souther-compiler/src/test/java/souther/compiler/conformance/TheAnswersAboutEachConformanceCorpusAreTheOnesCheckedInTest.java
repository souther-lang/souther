package souther.compiler.conformance;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * What this compiler answers about the conformance corpus is what the repository says it answers.
 *
 * <p>Nothing else here fails when an answer changes. The suite around this holds one rule each
 * against a fixture written for it, which is what makes a rule's own behavior checkable and is also
 * why none of them sees a change of answer over a model of the size someone writes: no fixture is
 * that size, and a measure that moved on one would move on none of them. That question used to be
 * answered by running the compiler over another repository and reading the two reports by eye,
 * which is a comparison nothing fails at.
 *
 * <p>So the answers are written down. A change that moves one is a change to the checked-in
 * document, made in the commit that moved it, and reviewed as part of it. That is the whole
 * mechanism: the value of it is not in this class but in the diff a rule's author has to show.
 *
 * <p>What it does not claim is that the answers are good ones. It records what they are.
 */
class TheAnswersAboutEachConformanceCorpusAreTheOnesCheckedInTest {

    /**
     * Rewrites every document instead of checking it. A deliberate act, spelled out, and it fails
     * afterwards: a run that rewrote what it was going to be measured against has not measured
     * anything, and one that said so quietly would read as a passing run.
     */
    private static final String UPDATE = "souther.conformance.update";

    private record Document(String name, String file, String actual) {}

    private static List<Document> documents() {
        List<Document> out = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            ConformanceCorpus.Analysed analysed = corpus.analyse();
            out.add(new Document(corpus.name(), corpus.name() + "/expected.report.json",
                    ConformanceSnapshot.report(analysed)));
            out.add(new Document(corpus.name(), corpus.name() + "/expected.diagnostics.txt",
                    ConformanceSnapshot.diagnostics(analysed)));
        }
        return out;
    }

    @Test
    void everyAnswerIsTheOneWrittenDown() {
        List<Document> documents = documents();
        if (Boolean.getBoolean(UPDATE)) {
            for (Document document : documents) {
                write(ConformanceCorpus.SOURCE_DIR.resolve(document.file()), document.actual());
            }
            throw new AssertionError("rewrote " + documents.size() + " expected document(s) under "
                    + ConformanceCorpus.SOURCE_DIR + ". Read the diff: it is what this change did to"
                    + " the compiler's answers. Then run again without -D" + UPDATE + ".");
        }
        List<String> differences = new ArrayList<>();
        for (Document document : documents) {
            String expected = read(document.file());
            if (!expected.equals(document.actual())) {
                differences.add(describe(document, expected));
            }
        }
        if (!differences.isEmpty()) {
            throw new AssertionError(String.join(System.lineSeparator() + System.lineSeparator(),
                    differences) + System.lineSeparator() + System.lineSeparator()
                    + "If the change that moved these is the change you meant to make, rerun with"
                    + " -D" + UPDATE + "=true and commit the rewritten documents with it.");
        }
    }

    /**
     * What moved, near enough to act on without opening the file.
     *
     * <p>The first line that differs and a few either side, rather than the whole document. A
     * report is thousands of lines and a difference in one of them is not something a reader finds
     * by being handed all of them — and the point of holding these here at all is that the answer
     * arrives in seconds, which a document nobody can read in seconds gives back.
     */
    private static String describe(Document document, String expected) {
        List<String> was = expected.lines().toList();
        List<String> now = document.actual().lines().toList();
        int at = 0;
        while (at < was.size() && at < now.size() && was.get(at).equals(now.get(at))) {
            at++;
        }
        StringBuilder said = new StringBuilder(document.file() + " is not what the compiler now"
                + " answers about " + document.name() + " (" + was.size() + " lines written down, "
                + now.size() + " now). First difference at line " + (at + 1) + ":");
        for (int i = Math.max(0, at - 2); i < Math.min(Math.max(was.size(), now.size()), at + 3);
                i++) {
            if (i < was.size() && i < now.size() && was.get(i).equals(now.get(i))) {
                said.append(System.lineSeparator()).append("      ").append(was.get(i));
            } else {
                if (i < was.size()) {
                    said.append(System.lineSeparator()).append("  was ").append(was.get(i));
                }
                if (i < now.size()) {
                    said.append(System.lineSeparator()).append("  now ").append(now.get(i));
                }
            }
        }
        return said.toString();
    }

    /** An expected document, or nothing where none has been written yet. */
    private static String read(String file) {
        try (var in = ConformanceCorpus.class.getResourceAsStream(
                ConformanceCorpus.ROOT + file)) {
            return in == null ? "" : new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static void write(Path path, String content) {
        try {
            Files.createDirectories(path.getParent());
            Files.writeString(path, content, StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
