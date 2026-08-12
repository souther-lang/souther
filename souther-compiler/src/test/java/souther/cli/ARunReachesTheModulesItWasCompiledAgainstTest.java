package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code run} resolves an import against the modules another compile already built, and runs against
 * their classes.
 *
 * <p>{@code run} used to be its own execution unit: one source, no module path, and a loader over the
 * application's rather than over the path. Each of the three showed as its own failure — the command
 * line read {@code -cp} as a second file, the compile reported the imported module as unknown, and a
 * behavior that built a value of that module's would have had no class to build it from. The three
 * are one wiring, so they are held here together: a fixture that only resolves would leave the third
 * unmeasured, which is why the behavior this runs returns a value whose class is on the path alone.
 */
class ARunReachesTheModulesItWasCompiledAgainstTest {

    @TempDir
    Path dir;

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

    private record Said(int code, String err, String out) {}

    private Said cli(String... args) {
        PrintStream originalErr = System.err;
        PrintStream originalOut = System.out;
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            int code = Main.dispatch(args);
            return new Said(code, err.toString(StandardCharsets.UTF_8),
                    out.toString(StandardCharsets.UTF_8));
        } finally {
            System.setErr(originalErr);
            System.setOut(originalOut);
        }
    }

    private Path source(String name, String text) throws Exception {
        Path file = dir.resolve(name);
        Files.writeString(file, text);
        return file;
    }

    /** The dependency, compiled on its own, as the project that owns it would ship it. */
    private Path builtCatalog() throws Exception {
        Path out = dir.resolve("catalog-classes");
        Said built = cli("compile", source("catalog.sou", CATALOG).toString(), "-d", out.toString());
        assertEquals(0, built.code(), built.err());
        return out;
    }

    /** The command line reads {@code -cp} as an option of its own and not as a second source. */
    @Test
    void runTakesAClassPathRatherThanReadingItAsASecondFile() throws Exception {
        Path path = builtCatalog();

        Said said = cli("run", source("enrollment.sou", ENROLLMENT).toString(),
                "-cp", path.toString(), "--behavior", "register", "--input", "\"c-1\"");

        assertFalse(said.err().contains("run takes a single .sou file"), said.err());
    }

    /** The import resolves against what is on the path, so the module is not reported as unknown. */
    @Test
    void anImportedModuleOnThePathIsNotUnknown() throws Exception {
        Path path = builtCatalog();

        Said said = cli("run", source("enrollment.sou", ENROLLMENT).toString(),
                "-cp", path.toString(), "--behavior", "register", "--input", "\"c-1\"");

        // not 2: a command line that refused the arguments never compiled, and every assertion
        // about what the compile did not say would hold over it
        assertFalse(said.code() == 2, said.err());
        assertFalse(said.err().contains("E1504"), said.err());
        assertFalse(said.err().contains("enrollment.catalog"), said.err());
    }

    /**
     * The behavior runs, and what it returns is a value of the module on the path.
     *
     * <p>This is the one the other two do not cover. A compile that resolves against the path does
     * not re-emit what it read there, so the class {@code Title} is defined nowhere in this
     * compilation's output; a loader that sits over the application's rather than over the path has
     * nothing to build the returned value from.
     */
    @Test
    void aBehaviorBuildsAValueWhoseClassIsOnThePathAlone() throws Exception {
        Path path = builtCatalog();

        Said said = cli("run", source("enrollment.sou", ENROLLMENT).toString(),
                "-cp", path.toString(), "--behavior", "register", "--input", "\"c-1\"");

        assertEquals(0, said.code(), said.err());
        assertEquals("\"Intro\"", said.out().trim(), said.err());
    }

    /** Without the path there is nowhere for the import to resolve, and that is still refused. */
    @Test
    void anImportedModuleWithNoPathIsStillRefused() throws Exception {
        Said said = cli("run", source("enrollment.sou", ENROLLMENT).toString(),
                "--behavior", "register", "--input", "\"c-1\"");

        assertEquals(1, said.code());
        assertTrue(said.err().contains("E1504"), said.err());
    }

    /**
     * The refusal says how {@code run} is given a module, which the diagnostic itself does not: what
     * E1504 states is that the module is in neither the sources nor the path, and which option
     * widens the path is this command line's to say.
     */
    @Test
    void aModuleRunCouldNotReachIsAnsweredWithHowToGiveItOne() throws Exception {
        Said said = cli("run", source("enrollment.sou", ENROLLMENT).toString(),
                "--lang", "en", "--behavior", "register", "--input", "\"c-1\"");

        assertTrue(said.err().contains("Unknown module `enrollment.catalog`"), said.err());
        assertTrue(said.err().contains("-cp"), said.err());
        assertTrue(said.err().contains("--class-path"), said.err());
    }

    /**
     * One line, whatever went unresolved.
     *
     * <p>Two unresolved imports are still one thing to do about them. This compile raises the first
     * error, so what arrives here is one diagnostic either way and the count is the line's own
     * arithmetic; an error carrying several — which the {@code example} rows already produce — is
     * what the guard in the CLI is written for.
     */
    @Test
    void theWayToGiveRunAModuleIsSaidOnce() throws Exception {
        String twoImports = """
                module enrollment.registration exposing (register)

                import enrollment.catalog ( CourseId, Title )
                import enrollment.term ( TermId )

                behavior register : (id: CourseId) -> Title
                    constructs Title

                let register (id) = Title("Intro")
                """;
        Said said = cli("run", source("enrollment.sou", twoImports).toString(),
                "--lang", "en", "--behavior", "register", "--input", "\"c-1\"");

        assertEquals(1, said.err().split("--class-path", -1).length - 1, said.err());
    }

    /**
     * Not into the JSON, where a reader takes one object per line and a sentence among them is a
     * line that parses as nothing. What a machine reader gets is the diagnostic and the exit code.
     */
    @Test
    void theHintIsNotWrittenIntoTheJsonOutput() throws Exception {
        Said said = cli("run", source("enrollment.sou", ENROLLMENT).toString(),
                "--format", "json", "--behavior", "register", "--input", "\"c-1\"");

        assertEquals(1, said.code());
        assertTrue(said.err().contains("E1504"), said.err());
        assertFalse(said.err().contains("--class-path"), said.err());
    }

    /** An error that is not an unresolved module is not answered with a class path. */
    @Test
    void anErrorThatIsNotAnUnreachedModuleGetsNoClassPathHint() throws Exception {
        String noSuchBehavior = """
                module enrollment.registration exposing (register)

                behavior register : (id: String) -> Title
                    constructs Title

                let register (id) = Title("Intro")
                """;
        Said said = cli("run", source("enrollment.sou", noSuchBehavior).toString(),
                "--lang", "en", "--behavior", "register", "--input", "\"c-1\"");

        assertEquals(1, said.code());
        assertFalse(said.err().contains("--class-path"), said.err());
    }
}
