package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.cli.CliProcess.Ran;
import souther.cli.backend.FakeBackend;
import souther.compiler.meta.ModuleMetadata;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther compile --target <target>} hands everything after the target to the installed
 * backend, and what the backend does is what the command does.
 *
 * <p>That everything is handed over is asked of the CLI run as a process, because arguments,
 * standard streams, the working directory, the environment and the exit status are facts about a
 * process, and the backend inherits the CLI's: only a process started from a shell has them to
 * pass on. Which backend is run, or why none is, is a question about what the CLI does with its
 * environment, and is asked of it in this JVM.
 */
class ACompileForAnInstalledTargetIsRunByItsBackendAsWrittenTest {

    private static final String HERE = ModuleMetadata.compilerVersion();

    @TempDir
    Path scratch;

    private Ran cli(Path workingDirectory, Map<String, String> environment,
                    Map<String, String> properties, String... args) throws Exception {
        return CliInProcess.run(scratch, workingDirectory, environment, properties, "", args);
    }

    private static Map<String, String> home(Path home) {
        return Map.of("SOUTHER_HOME", home.toString());
    }

    @Test
    void everythingAfterTheTargetReachesTheBackendAndWhatItDoesComesBack(@TempDir Path home,
                                                                         @TempDir Path work)
            throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "the-backend");

        Ran ran = CliProcess.run(scratch, work,
                Map.of("SOUTHER_HOME", home.toString(), "FAKE_ENV", "carried"), List.of(),
                "typed in", "compile", "--target", "fake", "--exit", "7", "--help", "-d", "out",
                "--component", "a.sou");

        assertEquals(7, ran.code(), ran.err());
        assertTrue(ran.out().contains("marker=the-backend\n"), ran.out());
        assertTrue(ran.out().contains("args=--exit|7|--help|-d|out|--component|a.sou\n"),
                ran.out());
        assertTrue(ran.out().contains("cwd=" + work.toRealPath() + "\n"), ran.out());
        assertTrue(ran.out().contains("env=carried\n"), ran.out());
        assertTrue(ran.out().contains("stdin=typed in\n"), ran.out());
        assertEquals("said-on-stderr", ran.err().strip());
    }

    /**
     * The same, from a run whose streams are not the process's: the backend is given pipes, and
     * what passes through them is what it would have read and written on inherited ones.
     */
    @Test
    void aRunOnStreamsOfItsOwnHandsTheBackendTheSame(@TempDir Path home, @TempDir Path work)
            throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "the-backend");

        Ran ran = CliInProcess.run(scratch, work,
                Map.of("SOUTHER_HOME", home.toString(), "FAKE_ENV", "carried"), Map.of(),
                "typed in", "compile", "--target", "fake", "--exit", "7", "a.sou");

        assertEquals(7, ran.code(), ran.err());
        assertTrue(ran.out().contains("marker=the-backend\n"), ran.out());
        assertTrue(ran.out().contains("args=--exit|7|a.sou\n"), ran.out());
        assertTrue(ran.out().contains("cwd=" + work.toRealPath() + "\n"), ran.out());
        assertTrue(ran.out().contains("env=carried\n"), ran.out());
        assertTrue(ran.out().contains("stdin=typed in\n"), ran.out());
        assertEquals("said-on-stderr", ran.err().strip());
    }

    /**
     * The home a run is given is searched before the directory a package names. That the first
     * of the directories searched wins, and that the packaged one is searched at all, are asked
     * without a backend run.
     */
    @Test
    void theHomeDirectoryStandsInForThePackagedOne(@TempDir Path home, @TempDir Path packaged,
                                                   @TempDir Path work) throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "from-home");
        FakeBackend.write(packaged.resolve("fake.jar"), "fake", HERE, "from-package");

        Ran both = cli(work, home(home), Map.of("souther.backends", packaged.toString()),
                "compile", "--target", "fake");

        assertEquals(0, both.code(), both.err());
        assertTrue(both.out().contains("marker=from-home\n"), both.out() + both.err());
    }

    @Test
    void aBackendBuiltForAnotherSoutherIsRefusedNamingBothAndNothingRuns(@TempDir Path home,
                                                                         @TempDir Path work)
            throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", "0.0.1-other", "never");

        Ran ran = cli(work, home(home), Map.of(), "compile", "--target", "fake");

        assertEquals(2, ran.code());
        assertEquals("", ran.out());
        assertTrue(ran.err().contains("0.0.1-other") && ran.err().contains(HERE), ran.err());
    }

    @Test
    void anUninstalledTargetIsRefusedNamingWhatIsInstalled(@TempDir Path home,
                                                           @TempDir Path work) throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "never");

        Ran ran = cli(work, home(home), Map.of(), "compile", "--target", "absent");

        assertEquals(2, ran.code());
        assertTrue(ran.err().contains("absent") && ran.err().contains("fake"), ran.err());
    }
}
