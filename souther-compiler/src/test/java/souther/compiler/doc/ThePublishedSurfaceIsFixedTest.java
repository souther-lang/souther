package souther.compiler.doc;

import souther.compiler.DefaultStdlib;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The standard library's published surface, written down. Every qualified name a module outside the
 * reserved namespace may write, with the parameter names and types it takes, checked against a
 * recorded copy.
 *
 * <p>What this catches is vocabulary drifting back in. The naming grammar the library follows is a
 * set of rules about words — the same word for the same operation, a settled term where one exists,
 * the behaviour in the name where languages disagree — and rules about words are enforced by reading
 * them, which nothing does on every commit. A snapshot does: adding, renaming or reordering anything
 * on the surface fails here, and the diff is the whole surface before and after, which is the form a
 * reader can judge the new name against its neighbours in.
 *
 * <p>What is recorded is the listing {@code souther api} prints, so a sugar such as {@code List.fold}
 * is held with the signature a reader is shown for it, and a change to what it takes or answers
 * changes this.
 *
 * <p>It is not a test of behaviour and does not stand in for one. Update it by running with
 * {@code -Dsouther.surface.update=true} once the change is the one intended.
 */
class ThePublishedSurfaceIsFixedTest {

    private static final String SNAPSHOT = "/souther/published-surface.txt";
    private static final Path SOURCE = Path.of("src/test/resources/souther/published-surface.txt");

    @Test
    void thePublishedSurfaceMatchesTheRecordedOne() throws IOException {
        String current = render();
        if (Boolean.getBoolean("souther.surface.update")) {
            Files.createDirectories(SOURCE.getParent());
            Files.writeString(SOURCE, current, StandardCharsets.UTF_8);
        }
        assertEquals(recorded(), current,
                "the standard library's published surface changed. If that is the intention, rerun"
                        + " with -Dsouther.surface.update=true and read the diff as a whole: a new"
                        + " name has to sit beside the ones already there.");
    }

    @Test
    void theSnapshotHoldsWhatIsPublishedAndNothingElse() {
        String current = render();
        assertTrue(current.contains("List.fold("), "the `List.fold` sugar is part of the surface");
        assertFalse(current.contains("List.foldFrom"),
                "a private declaration is not on the surface, so it is not in the snapshot");
        assertEquals(DefaultStdlib.get().published().size(), current.lines().filter(l -> !l.isBlank()).count(),
                "one line per published name");
    }

    /** What {@code souther api} lists with nothing asked: one line per published name, in
     *  qualifier then declaration order. */
    private static String render() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = ApiCommand.run(new String[]{},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));
        assertEquals(0, code, err.toString(StandardCharsets.UTF_8));
        return out.toString(StandardCharsets.UTF_8);
    }

    private static String recorded() {
        try (InputStream in = ThePublishedSurfaceIsFixedTest.class.getResourceAsStream(SNAPSHOT)) {
            if (in == null) {
                throw new IllegalStateException("no recorded surface at " + SNAPSHOT
                        + " — run with -Dsouther.surface.update=true to write it");
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
