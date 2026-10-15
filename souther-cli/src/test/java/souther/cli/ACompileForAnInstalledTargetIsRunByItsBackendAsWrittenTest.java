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
 * backend, and what the backend does is what the command does. The CLI is run as a process here,
 * because arguments, standard streams, the working directory, the environment and the exit status
 * are facts about a process, and a backend is one.
 */
class ACompileForAnInstalledTargetIsRunByItsBackendAsWrittenTest {

    private static final String HERE = ModuleMetadata.compilerVersion();

    @TempDir
    Path scratch;

    private Ran cli(Path workingDirectory, Map<String, String> environment,
                    List<String> jvmProperties, String stdin, String... args) throws Exception {
        return CliProcess.run(scratch, workingDirectory, environment, jvmProperties, stdin, args);
    }

    private static Map<String, String> home(Path home) {
        return Map.of("SOUTHER_HOME", home.toString());
    }

    @Test
    void everythingAfterTheTargetReachesTheBackendAndWhatItDoesComesBack(@TempDir Path home,
                                                                         @TempDir Path work)
            throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "the-backend");

        Ran ran = cli(work, Map.of("SOUTHER_HOME", home.toString(), "FAKE_ENV", "carried"),
                List.of(), "typed in", "compile", "--target", "fake", "--exit", "7", "--help",
                "-d", "out", "--component", "a.sou");

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
     * The home a run is given is searched before the directory a package names. That the first
     * of the directories searched wins, and that the packaged one is searched at all, are asked
     * without a backend run.
     */
    @Test
    void theHomeDirectoryStandsInForThePackagedOne(@TempDir Path home, @TempDir Path packaged,
                                                   @TempDir Path work) throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "from-home");
        FakeBackend.write(packaged.resolve("fake.jar"), "fake", HERE, "from-package");

        Ran both = cli(work, home(home), List.of("-Dsouther.backends=" + packaged), "", "compile",
                "--target", "fake");

        assertTrue(both.out().contains("marker=from-home\n"), both.out() + both.err());
    }

    @Test
    void aBackendBuiltForAnotherSoutherIsRefusedNamingBothAndNothingRuns(@TempDir Path home,
                                                                         @TempDir Path work)
            throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", "0.0.1-other", "never");

        Ran ran = cli(work, home(home), List.of(), "", "compile", "--target", "fake");

        assertEquals(2, ran.code());
        assertEquals("", ran.out());
        assertTrue(ran.err().contains("0.0.1-other") && ran.err().contains(HERE), ran.err());
    }

    @Test
    void anUninstalledTargetIsRefusedNamingWhatIsInstalled(@TempDir Path home,
                                                           @TempDir Path work) throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "never");

        Ran ran = cli(work, home(home), List.of(), "", "compile", "--target", "absent");

        assertEquals(2, ran.code());
        assertTrue(ran.err().contains("absent") && ran.err().contains("fake"), ran.err());
    }
}
