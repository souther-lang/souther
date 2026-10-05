package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.cli.backend.FakeBackend;
import souther.compiler.meta.ModuleMetadata;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther compile --target <target>} hands everything after the target to the installed
 * backend, and what the backend does is what the command does. The CLI is run as a process here,
 * because arguments, standard streams, the working directory, the environment and the exit status
 * are facts about a process, and a backend is one.
 */
class ACompileForAnInstalledTargetIsRunByItsBackendAsWrittenTest {

    private static final String HERE = ModuleMetadata.compilerVersion();

    private record Ran(int code, String out, String err) {}

    private static Ran cli(Path workingDirectory, Map<String, String> environment,
                           List<String> jvmProperties, String stdin, String... args)
            throws Exception {
        List<String> command = new ArrayList<>();
        command.add(Path.of(System.getProperty("java.home"), "bin", "java").toString());
        command.addAll(jvmProperties);
        command.addAll(List.of("-cp", System.getProperty("java.class.path"), "souther.cli.Main"));
        command.addAll(List.of(args));
        Path out = Files.createTempFile("cli", ".out");
        Path err = Files.createTempFile("cli", ".err");
        ProcessBuilder builder = new ProcessBuilder(command).directory(workingDirectory.toFile())
                .redirectOutput(out.toFile()).redirectError(err.toFile());
        builder.environment().remove("SOUTHER_HOME");
        builder.environment().remove("SOUTHER_LANG");
        builder.environment().putAll(environment);
        Process process = builder.start();
        try (var in = process.getOutputStream()) {
            in.write(stdin.getBytes(StandardCharsets.UTF_8));
        }
        int code = process.waitFor();
        return new Ran(code, Files.readString(out), Files.readString(err));
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

    @Test
    void aBackendThatSucceedsSucceeds(@TempDir Path home, @TempDir Path work) throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "ok");

        Ran ran = cli(work, home(home), List.of(), "", "compile", "--target", "fake");

        assertEquals(0, ran.code(), ran.err());
    }

    @Test
    void theHomeDirectoryStandsInForThePackagedOne(@TempDir Path home, @TempDir Path packaged,
                                                   @TempDir Path work) throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "from-home");
        FakeBackend.write(packaged.resolve("fake.jar"), "fake", HERE, "from-package");
        String property = "-Dsouther.backends=" + packaged;

        Ran both = cli(work, home(home), List.of(property), "", "compile", "--target", "fake");
        Ran packagedOnly = cli(work, Map.of(), List.of(property), "", "compile", "--target",
                "fake");

        assertTrue(both.out().contains("marker=from-home\n"), both.out() + both.err());
        assertTrue(packagedOnly.out().contains("marker=from-package\n"),
                packagedOnly.out() + packagedOnly.err());
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

    @Test
    void aProjectNamingAnotherSoutherRefusesTheTargetToo(@TempDir Path home,
                                                         @TempDir Path work) throws Exception {
        FakeBackend.write(home.resolve("backends/fake.jar"), "fake", HERE, "never");
        Files.writeString(work.resolve(ProjectVersion.FILE), "0.0.1-other\n");

        Ran ran = cli(work, home(home), List.of(), "", "compile", "--target", "fake");

        assertEquals(2, ran.code());
        assertFalse(ran.out().contains("marker="), ran.out());
        assertTrue(ran.err().contains("0.0.1-other"), ran.err());
    }

    @Test
    void aTargetWrittenWithNoNameIsRefused(@TempDir Path work) throws Exception {
        Ran bare = cli(work, Map.of(), List.of(), "", "compile", "--target");
        Ran option = cli(work, Map.of(), List.of(), "", "compile", "--target", "--help");

        assertEquals(2, bare.code());
        assertEquals(2, option.code());
        assertTrue(bare.err().contains("--target"), bare.err());
    }

    @Test
    void theTargetIsReadOnlyAsTheFirstArgument(@TempDir Path work) throws Exception {
        Ran ran = cli(work, Map.of(), List.of(), "", "compile", "a.sou", "--target", "jvm");

        assertEquals(2, ran.code());
        assertTrue(ran.err().contains("--target"), ran.err());
    }

    @Test
    void theJvmTargetIsTheCompileThereAlwaysWas(@TempDir Path work) throws Exception {
        Path source = Files.writeString(work.resolve("m.sou"), """
                module m
                data X = { a: Int }
                """);
        Path plain = Files.createDirectories(work.resolve("plain"));
        Path named = Files.createDirectories(work.resolve("named"));

        Ran without = cli(work, Map.of(), List.of(), "", "compile", "-d", plain.toString(),
                source.toString());
        Ran with = cli(work, Map.of(), List.of(), "", "compile", "--target", "jvm", "-d",
                named.toString(), source.toString());

        assertEquals(0, without.code(), without.err());
        assertEquals(0, with.code(), with.err());
        assertEquals(listing(plain), listing(named));
        assertFalse(listing(named).isEmpty());
    }

    @Test
    void theJvmTargetStillRefusesAnOptionTheJvmDoesNotHave(@TempDir Path work)
            throws Exception {
        Ran ran = cli(work, Map.of(), List.of(), "", "compile", "--target", "jvm", "--component",
                "m.sou");

        assertEquals(2, ran.code());
        assertTrue(ran.err().contains("--component"), ran.err());
    }

    private static List<String> listing(Path root) throws IOException {
        try (var files = Files.walk(root)) {
            return files.filter(Files::isRegularFile).map(file -> root.relativize(file).toString())
                    .sorted().toList();
        }
    }
}
