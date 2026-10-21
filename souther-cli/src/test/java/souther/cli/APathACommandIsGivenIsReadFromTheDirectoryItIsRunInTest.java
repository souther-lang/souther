package souther.cli;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.cli.CliProcess.Ran;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relative path a command is given is read from the directory the run is in, which is the
 * {@link Environment}'s and not the JVM's.
 *
 * <p>Run in this JVM from a directory it does not run in, so a path read against the JVM's
 * directory names a file that is not there, and one written against it lands outside the run's.
 * Every command that takes a path is asked with a relative one: the sources, the directory written
 * to and the class path of {@code compile}, the file and the class path of {@code run}, the sources
 * of {@code examples}, the files of {@code fmt} and the class path of {@code japi}. The directory
 * {@code init} writes to is asked where {@code init} is, since a run of it here has no release to
 * write.
 */
class APathACommandIsGivenIsReadFromTheDirectoryItIsRunInTest {

    @TempDir
    Path dir;

    private Path work;

    private static final String CATALOG = """
            module enrollment.catalog exposing (CourseId, Title)

            data CourseId = String

            data Title = String
            """;

    private static final String ENROLLMENT = """
            module enrollment.registration exposing (register)

            import enrollment.catalog ( CourseId, Title )

            behavior register : (id: CourseId) -> Title
                constructs Title

            let register (id) = Title("Intro")
            """;

    @BeforeEach
    void layOut() throws IOException {
        work = Files.createDirectories(dir.resolve("work"));
        Files.writeString(work.resolve("catalog.sou"), CATALOG);
        Files.writeString(work.resolve("enrollment.sou"), ENROLLMENT);
    }

    private Ran souther(String... args) {
        return CliInProcess.run(dir, work, Map.of(), Map.of(), "", args);
    }

    /** The catalog, compiled into {@code classes} under the run's directory. */
    private void compiledCatalog() {
        Ran built = souther("compile", "catalog.sou", "-d", "classes");
        assertEquals(0, built.code(), built.err());
    }

    /** The control: the run's directory is not this JVM's, and the sources are not in this JVM's. */
    @Test
    void theRunIsInADirectoryThisJvmDoesNotRunIn() {
        assertNotEquals(work.resolve("catalog.sou"), Path.of("catalog.sou").toAbsolutePath());
        assertFalse(Files.exists(Path.of("catalog.sou")));
    }

    @Test
    void compileReadsItsSourcesAndClassPathAndWritesItsClassesThere() throws IOException {
        compiledCatalog();
        assertTrue(Files.isDirectory(work.resolve("classes")));

        Ran built = souther("compile", "enrollment.sou", "-cp", "classes", "-d", "out");

        assertEquals(0, built.code(), built.err());
        assertTrue(Files.isDirectory(work.resolve("out")));
        try (var written = Files.list(work.resolve("out"))) {
            assertTrue(written.findAny().isPresent(), built.out());
        }
    }

    @Test
    void runReadsItsFileAndClassPathThere() {
        compiledCatalog();

        Ran ran = souther("run", "enrollment.sou", "-cp", "classes", "--behavior", "register",
                "--input", "\"c-1\"");

        assertEquals(0, ran.code(), ran.err());
        assertEquals("\"Intro\"", ran.out().trim(), ran.err());
    }

    @Test
    void examplesReadsItsSourcesThere() {
        Ran examined = souther("examples", "catalog.sou");

        assertEquals(0, examined.code(), examined.err());
    }

    @Test
    void fmtReadsItsFilesThere() {
        Ran formatted = souther("fmt", "catalog.sou");

        assertEquals(0, formatted.code(), formatted.err());
        assertTrue(formatted.out().contains("module enrollment.catalog"), formatted.out());
    }

    @Test
    void japiReadsItsClassPathThere() {
        compiledCatalog();

        Ran described = souther("japi", "enrollment.catalog", "-cp", "classes");

        assertEquals(0, described.code(), described.err());
    }
}
