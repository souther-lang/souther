package souther.cli;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.cli.CliProcess.Ran;
import souther.cli.backend.Backends;
import souther.cli.backend.Configured;
import souther.cli.backend.FakeBackend;
import souther.cli.backend.LocalRepository;
import souther.cli.backend.Repository;
import souther.cli.backend.Unavailable;
import souther.compiler.diag.Messages;
import souther.compiler.meta.ModuleMetadata;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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

    @TempDir
    Path scratch;

    private LocalRepository repository;

    @BeforeEach
    void start() throws IOException {
        repository = LocalRepository.start();
    }

    @AfterEach
    void stop() {
        repository.close();
    }

    private Path fetchedTo() {
        return CliProcess.userHome(scratch).resolve(".souther/backends");
    }

    private Ran cli(Map<String, String> environment, String... args) throws Exception {
        return CliInProcess.run(scratch, work, environment,
                Map.of("souther.repository", repository.uri().toString()), "", args);
    }

    private void released(String marker) throws IOException {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE,
                FakeBackend.write(work.resolve("served.jar"), "wasm", HERE, marker));
    }

    @Test
    void anEmptyHomeFetchesTheBackendAndRunsIt() throws Exception {
        released("fetched-backend");

        Ran first = cli(Map.of(), "compile", "--target", "wasm", "--exit", "3", "a.sou");

        assertEquals(3, first.code(), first.err());
        assertTrue(first.out().contains("marker=fetched-backend\n"), first.out());
        assertTrue(first.out().contains("args=--exit|3|a.sou\n"), first.out());
        assertFalse(first.out().contains(WASM), first.out());
        assertTrue(first.err().contains(WASM) && first.err().contains("0.1.0"), first.err());
        assertTrue(Files.isRegularFile(fetchedTo().resolve("wasm-" + HERE + ".jar")));
    }

    /** Asked of {@code backend fetch}, which writes where a compile does and runs no backend. */
    @Test
    void theHomeSoutherNamesIsWhereABackendIsFetchedTo() throws Exception {
        released("into-souther-home");
        Path home = work.resolve("souther-home");

        Ran ran = cli(Map.of("SOUTHER_HOME", home.toString()), "backend", "fetch", "wasm");

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
        Map<String, String> properties = Map.of("souther.repository", repository.uri().toString(),
                "souther.backends", packaged.toString());
        String metadata = repository.uri().resolve(
                "org/souther-lang/" + WASM + "/maven-metadata.xml").toString();

        Ran english = CliInProcess.run(scratch, work, Map.of(), properties, "", "compile",
                "--target", "wasm");
        Ran japanese = CliInProcess.run(scratch, work, Map.of("SOUTHER_LANG", "ja"), properties,
                "", "compile", "--target", "wasm");

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
    void aRepositoryNamedOverPlainHttpElsewhereIsNotAskedAndNamedAsItWasRead() throws Exception {
        String named = "http://repository.example/maven2/";

        Ran ran = CliInProcess.run(scratch, work, Map.of(), Map.of("souther.repository", named),
                "", "compile", "--target", "wasm");

        assertEquals(2, ran.code());
        assertTrue(ran.err().contains("souther.repository") && ran.err().contains(named),
                ran.err());
        assertFalse(Files.exists(fetchedTo()), "a fetch that could ask nothing made " + fetchedTo());
    }

    /** A setting written one way, as a run is given it. */
    private record Written(String setting, Map<String, String> environment,
                           Map<String, String> properties) {}

    @Test
    void aPasswordInASettingIsNeverRepeatedHoweverTheSettingIsWritten() throws Exception {
        String password = "s3cret-pw";
        // Well formed and not: no masking of what was written could be relied on for the last
        // three, so what is shown has to be what was read and never what was written.
        List<String> values = List.of("http://alice:" + password + "@proxy.example:8080",
                "http://alice:se/" + password + "@proxy.example:8080",
                "http://alice:pa@" + password + "@proxy.example:8080",
                "alice:" + password + "@proxy.example:8080");
        List<Written> settings = new ArrayList<>();
        for (String value : values) {
            settings.add(new Written("HTTPS_PROXY", Map.of("HTTPS_PROXY", value), Map.of()));
            settings.add(new Written("souther.repository", Map.of(), Map.of("souther.repository",
                    value.replace("proxy.example:8080", "nexus.example/maven2/"))));
        }
        // What a run says of a setting it cannot use is the lines below, in either language, and
        // they are asked of every spelling here; each command is run once for each kind of
        // setting, which is where the settings are read from what a run is given.
        for (Written written : settings) {
            for (String lang : List.of("en", "ja")) {
                String said = unusable(written, lang);
                assertFalse(said.contains(password), written + " " + lang + said);
                assertTrue(said.contains(written.setting()), said);
            }
        }
        assertRefusedWithout(password, settings.get(0), "en", "compile", "--target", "wasm");
        assertRefusedWithout(password, settings.get(1), "ja", "backend", "fetch", "wasm");
    }

    /**
     * The lines a compile says where {@code written} names no repository it can use, in
     * {@code lang}; the ones {@code backend fetch} says are among them.
     */
    private static String unusable(Written written, String lang) {
        Configured configured = Repository.configured(written.environment(),
                written.properties());
        Configured.Unusable unusable = assertInstanceOf(Configured.Unusable.class, configured);
        Locale locale = Messages.resolveLocale(new Messages.Named(lang, false));
        StringBuilder said = new StringBuilder();
        for (Unavailable.Line line : Unavailable.of(new Backends.Absent("wasm", HERE, List.of()),
                unusable.why(), unusable.name())) {
            said.append(Messages.get(line.key(), locale, line.array())).append('\n');
        }
        return said.toString();
    }

    private void assertRefusedWithout(String password, Written written, String lang,
                                      String... args) throws Exception {
        Map<String, String> environment = new HashMap<>(written.environment());
        environment.put("SOUTHER_LANG", lang);

        Ran ran = CliInProcess.run(scratch, work, environment, written.properties(), "", args);

        String said = ran.out() + ran.err();
        assertEquals(2, ran.code(), said);
        assertFalse(said.contains(password), written + " " + List.of(args) + said);
        assertTrue(said.contains(written.setting()), said);
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
}
