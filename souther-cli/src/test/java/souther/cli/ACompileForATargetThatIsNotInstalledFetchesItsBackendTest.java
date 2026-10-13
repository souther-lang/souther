package souther.cli;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.cli.CliProcess.Ran;
import souther.cli.backend.FakeBackend;
import souther.cli.backend.LocalRepository;
import souther.compiler.meta.ModuleMetadata;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther compile --target <target>} for a target no directory holds fetches its backend from
 * the repository and runs it; {@code souther backend fetch} fetches one and compiles nothing; and a
 * target neither installed nor fetched is refused naming where it was looked for and what the
 * repository answered.
 */
class ACompileForATargetThatIsNotInstalledFetchesItsBackendTest {

    private static final String HERE = ModuleMetadata.compilerVersion();
    private static final String WASM = "souther-wasm-compiler";

    @TempDir
    Path work;

    private LocalRepository repository;
    private Path userHome;

    @BeforeEach
    void start() throws IOException {
        repository = LocalRepository.start();
        userHome = Files.createDirectories(work.resolve("user"));
    }

    @AfterEach
    void stop() {
        repository.close();
    }

    private Path fetchedTo() {
        return userHome.resolve(".souther/backends");
    }

    private Ran cli(Map<String, String> environment, String... args) throws Exception {
        return CliProcess.run(work, environment,
                List.of("-Duser.home=" + userHome, "-Dsouther.repository=" + repository.uri()),
                "", args);
    }

    private void released(String marker) throws IOException {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE,
                FakeBackend.write(work.resolve("served.jar"), "wasm", HERE, marker));
    }

    @Test
    void anEmptyHomeFetchesTheBackendAndRunsItAndTheNextCompileAsksNothing() throws Exception {
        released("fetched-backend");

        Ran first = cli(Map.of(), "compile", "--target", "wasm", "--exit", "3", "a.sou");

        assertEquals(3, first.code(), first.err());
        assertTrue(first.out().contains("marker=fetched-backend\n"), first.out());
        assertTrue(first.out().contains("args=--exit|3|a.sou\n"), first.out());
        assertFalse(first.out().contains(WASM), first.out());
        assertTrue(first.err().contains(WASM) && first.err().contains("0.1.0"), first.err());
        assertTrue(Files.isRegularFile(fetchedTo().resolve("wasm-" + HERE + ".jar")));

        int asked = repository.asked().size();
        Ran second = cli(Map.of(), "compile", "--target", "wasm");

        assertEquals(0, second.code(), second.err());
        assertEquals("said-on-stderr", second.err().strip());
        assertEquals(asked, repository.asked().size());
    }

    @Test
    void theHomeSoutherNamesIsWhereABackendIsFetchedTo() throws Exception {
        released("into-souther-home");
        Path home = work.resolve("souther-home");

        Ran ran = cli(Map.of("SOUTHER_HOME", home.toString()), "compile", "--target", "wasm");

        assertEquals(0, ran.code(), ran.err());
        assertTrue(Files.isRegularFile(home.resolve("backends/wasm-" + HERE + ".jar")));
        assertFalse(Files.exists(fetchedTo()));
    }

    @Test
    void aCompileToldToFetchNothingAsksNothingAndSaysWhereItLooked() throws Exception {
        released("never");

        Ran ran = cli(Map.of(Main.OFFLINE, "1"), "compile", "--target", "wasm");

        assertEquals(2, ran.code());
        assertEquals("", ran.out());
        assertEquals(List.of(), repository.asked());
        assertTrue(ran.err().contains(fetchedTo().toString()), ran.err());
        assertTrue(ran.err().contains(Main.OFFLINE), ran.err());
        assertTrue(ran.err().contains("souther backend fetch wasm"), ran.err());
    }

    @Test
    void anUnpublishedTargetIsRefusedNamingEachDirectoryAndTheAnswerInEitherLanguage()
            throws Exception {
        Path packaged = Files.createDirectories(work.resolve("packaged"));
        FakeBackend.write(packaged.resolve("native.jar"), "native", HERE, "never");
        List<String> properties = List.of("-Duser.home=" + userHome,
                "-Dsouther.repository=" + repository.uri(), "-Dsouther.backends=" + packaged);
        String metadata = repository.uri().resolve(
                "org/souther-lang/" + WASM + "/maven-metadata.xml").toString();

        Ran english = CliProcess.run(work, Map.of(), properties, "", "compile", "--target",
                "wasm");
        Ran japanese = CliProcess.run(work, Map.of("SOUTHER_LANG", "ja"), properties, "",
                "compile", "--target", "wasm");

        for (Ran ran : List.of(english, japanese)) {
            assertEquals(2, ran.code());
            assertTrue(ran.err().contains(fetchedTo().toString()), ran.err());
            assertTrue(ran.err().contains(packaged.toString()), ran.err());
            assertTrue(ran.err().contains("native"), ran.err());
            assertTrue(ran.err().contains(metadata), ran.err());
        }
        assertEquals(english.err().lines().count(), japanese.err().lines().count(),
                english.err() + japanese.err());
        assertTrue(japanese.err().contains("公開されていません"), japanese.err());
    }

    @Test
    void aRepositoryNamedOverPlainHttpElsewhereIsNotAskedAndNamedAsItWasSet() throws Exception {
        String named = "http://repository.example/maven2/";

        Ran ran = CliProcess.run(work, Map.of(), List.of("-Duser.home=" + userHome,
                "-Dsouther.repository=" + named), "", "compile", "--target", "wasm");

        assertEquals(2, ran.code());
        assertTrue(ran.err().contains("souther.repository") && ran.err().contains(named),
                ran.err());
        assertFalse(Files.exists(fetchedTo()), "a fetch that could ask nothing made " + fetchedTo());
    }

    @Test
    void aTargetInstalledTwiceIsRefusedAndNothingIsFetchedInItsPlace() throws Exception {
        released("never");
        FakeBackend.write(fetchedTo().resolve("a.jar"), "wasm", HERE, "a");
        FakeBackend.write(fetchedTo().resolve("b.jar"), "wasm", HERE, "b");

        Ran ran = cli(Map.of(), "compile", "--target", "wasm");

        assertEquals(2, ran.code());
        assertEquals(List.of(), repository.asked());
        assertTrue(ran.err().contains("a.jar") && ran.err().contains("b.jar"), ran.err());
    }

    @Test
    void theFetchCommandFetchesAndCompilesNothing() throws Exception {
        released("fetched-ahead");

        Ran ran = cli(Map.of(Main.OFFLINE, "1"), "backend", "fetch", "wasm");

        assertEquals(0, ran.code(), ran.err());
        assertTrue(ran.out().contains(WASM) && ran.out().contains("0.1.0"), ran.out());
        assertFalse(ran.out().contains("marker="), ran.out());
        assertTrue(Files.isRegularFile(fetchedTo().resolve("wasm-" + HERE + ".jar")));

        Ran again = cli(Map.of(), "backend", "fetch", "wasm");
        String jar = "/maven2/" + LocalRepository.path(WASM, "0.1.0", "cli", "jar");

        assertEquals(0, again.code(), again.err());
        assertTrue(again.out().contains("already installed"), again.out());
        assertEquals(1, repository.asked().stream().filter(jar::equals).count());
    }

    @Test
    void theFetchCommandSaysWhatTheRepositoryAnswered() throws Exception {
        Ran ran = cli(Map.of(), "backend", "fetch", "wasm");

        assertEquals(2, ran.code());
        assertTrue(ran.err().contains("maven-metadata.xml"), ran.err());
    }

    @Test
    void theFetchCommandTakesFetchAndATargetAndNothingElse() throws Exception {
        for (List<String> line : List.of(List.of("backend"), List.of("backend", "fetch"),
                List.of("backend", "get", "wasm"), List.of("backend", "fetch", "wasm", "x"),
                List.of("backend", "fetch", "jvm"))) {
            Ran ran = cli(Map.of(), line.toArray(String[]::new));

            assertEquals(2, ran.code(), line + ran.err());
        }
        assertEquals(List.of(), repository.asked());
    }
}
