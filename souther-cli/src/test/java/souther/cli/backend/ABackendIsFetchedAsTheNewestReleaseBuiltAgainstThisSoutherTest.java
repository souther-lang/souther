package souther.cli.backend;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFileAttributeView;
import java.nio.file.attribute.PosixFilePermissions;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.stream.Stream;

import static java.nio.charset.StandardCharsets.ISO_8859_1;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which release of a target's backend is fetched, where it is put, and what is said where none is.
 * The repository is one served on the loopback address for the test, in Central's layout.
 */
class ABackendIsFetchedAsTheNewestReleaseBuiltAgainstThisSoutherTest {

    private static final String HERE = "9.9.9";
    private static final String OTHER = "9.9.8";
    private static final String WASM = "souther-wasm-compiler";
    private static final String NATIVE = "souther-native-compiler";

    @TempDir
    Path work;

    private LocalRepository repository;
    private Path home;
    private Backends backends;

    @BeforeEach
    void start() throws IOException {
        repository = LocalRepository.start();
        home = work.resolve("home/backends");
        backends = new Backends(List.of(home));
    }

    @AfterEach
    void stop() {
        repository.close();
    }

    private Path jar(String name, String target, String southerVersion) throws IOException {
        return FakeBackend.write(work.resolve("served/" + name + ".jar"), target, southerVersion,
                name);
    }

    /** The repository, where a download with nothing arriving for a second has stopped. */
    private Central central() {
        return Central.at(repository.uri(), Duration.ofSeconds(1));
    }

    private BackendFetch.Outcome fetch(String target) throws Exception {
        return BackendFetch.whereAbsent(backends, central(), target, HERE,
                release -> { });
    }

    private Central.Failure failed(String target) throws Exception {
        return assertInstanceOf(BackendFetch.Failed.class, fetch(target)).failure();
    }

    /** What the directory holds besides the lock, by name. */
    private List<String> held() throws IOException {
        try (Stream<Path> listed = Files.list(home)) {
            return listed.map(path -> path.getFileName().toString())
                    .filter(name -> !name.equals(".fetching.lock")).sorted().toList();
        }
    }

    @Test
    void theNewestReleaseBuiltAgainstThisSoutherIsFetchedAndNotTheNewestRelease()
            throws Exception {
        repository.metadata(WASM, "0.2.1", "0.1.0", "0.10.0", "0.2.0", "0.1.1", "0.2.2-rc1",
                "0.3.0-SNAPSHOT");
        repository.release(WASM, "0.1.0", "cli", OTHER, jar("r010", "wasm", OTHER));
        repository.release(WASM, "0.1.1", "cli", HERE, jar("r011", "wasm", HERE));
        repository.release(WASM, "0.2.0", "cli", OTHER, jar("r020", "wasm", OTHER));
        repository.release(WASM, "0.2.1", "cli", HERE, jar("r021", "wasm", HERE));
        repository.release(WASM, "0.2.2-rc1", "cli", OTHER, jar("r022rc1", "wasm", OTHER));
        repository.release(WASM, "0.10.0", "cli", OTHER, jar("r0100", "wasm", OTHER));
        repository.release(WASM, "0.3.0-SNAPSHOT", "cli", HERE, jar("snapshot", "wasm", HERE));

        BackendFetch.Fetched fetched = assertInstanceOf(BackendFetch.Fetched.class,
                fetch("wasm"));

        assertEquals("0.2.1", fetched.release().version());
        Path installed = home.resolve("wasm-" + HERE + ".jar");
        assertEquals(new Backends.Backend("wasm", HERE, installed), fetched.backend());
        assertEquals(Files.readString(work.resolve("served/r021.jar"), ISO_8859_1),
                Files.readString(installed, ISO_8859_1));
        assertEquals(List.of("wasm-" + HERE + ".jar"), held());
        assertEquals(fetched.backend(),
                assertInstanceOf(Backends.Found.class, backends.find("wasm", HERE)).backend());
        assertTrue(repository.asked().stream().noneMatch(path -> path.contains("SNAPSHOT")),
                repository.asked().toString());
        if (Files.getFileStore(installed).supportsFileAttributeView(PosixFileAttributeView.class)) {
            assertEquals("rw-r--r--",
                    PosixFilePermissions.toString(Files.getPosixFilePermissions(installed)));
        }
    }

    @Test
    void aReleaseWhosePomStatesNoSoutherIsReadThroughItsParent() throws Exception {
        repository.metadata(NATIVE, "0.1.0");
        repository.pom(NATIVE, "0.1.0", LocalRepository.inheriting(NATIVE, "0.1.0",
                "souther-native-parent", "0.1.0"));
        repository.pom("souther-native-parent", "0.1.0",
                LocalRepository.builtAgainst("souther-native-parent", "0.1.0", HERE));
        repository.jar(NATIVE, "0.1.0", "backend", jar("native", "native", HERE));

        BackendFetch.Fetched fetched = assertInstanceOf(BackendFetch.Fetched.class,
                fetch("native"));

        assertEquals(home.resolve("native-" + HERE + ".jar"), fetched.backend().jar());
    }

    @Test
    void aPomThatStatesNoSoutherAndNamesNoParentIsUnreadable() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.put(LocalRepository.path(WASM, "0.1.0", null, "pom"),
                "<project><artifactId>x</artifactId></project>");

        assertInstanceOf(Central.Failure.Unreadable.class, failed("wasm"));
    }

    @Test
    void aSoutherVersionLeftAsAnExpressionIsUnreadable() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.pom(WASM, "0.1.0",
                LocalRepository.builtAgainst(WASM, "0.1.0", "${project.version}"));

        assertInstanceOf(Central.Failure.Unreadable.class, failed("wasm"));
    }

    @Test
    void noReleaseBuiltAgainstThisSoutherNamesTheReleasesThereAre() throws Exception {
        repository.metadata(WASM, "0.2.0", "0.1.0");
        repository.release(WASM, "0.1.0", "cli", OTHER, jar("a", "wasm", OTHER));
        repository.release(WASM, "0.2.0", "cli", OTHER, jar("b", "wasm", OTHER));

        assertEquals(new Central.Failure.NoneBuilt(HERE, List.of("0.1.0", "0.2.0")),
                failed("wasm"));
        assertEquals(List.of(), held());
    }

    @Test
    void aTargetWithNoMetadataIsUnpublishedAndOneWithOnlySnapshotsIsToo() throws Exception {
        assertInstanceOf(Central.Failure.Unpublished.class, failed("wasm"));

        repository.metadata(NATIVE, "0.1.0-SNAPSHOT");
        assertInstanceOf(Central.Failure.Unpublished.class, failed("native"));
    }

    @Test
    void aTargetNoArtifactIsKnownForAsksNothing() throws Exception {
        assertEquals(new Central.Failure.Unregistered("llvm"), failed("llvm"));
        assertEquals(List.of(), repository.asked());
    }

    @Test
    void aRepositoryThatIsNotThereIsUnreachable() throws Exception {
        repository.close();

        Central.Failure failure = failed("wasm");

        assertInstanceOf(Central.Failure.Unreachable.class, failure);
    }

    @Test
    void metadataThatIsNotXmlOrDeclaresADoctypeIsUnreadable() throws Exception {
        repository.put("org/souther-lang/" + WASM + "/maven-metadata.xml", "<metadata><vers");
        assertInstanceOf(Central.Failure.Unreadable.class, failed("wasm"));

        repository.put("org/souther-lang/" + WASM + "/maven-metadata.xml", """
                <?xml version="1.0"?>
                <!DOCTYPE metadata [ <!ENTITY v "0.1.0"> ]>
                <metadata><versioning><versions><version>&v;</version></versions></versioning>
                </metadata>
                """);
        assertInstanceOf(Central.Failure.Unreadable.class, failed("wasm"));
    }

    @Test
    void aJarAnsweredWithAnErrorLeavesNothingBehind() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("a", "wasm", HERE));
        repository.answer(WASM, "0.1.0", "cli", 503);

        Central.Failure failure = failed("wasm");

        assertEquals(503, assertInstanceOf(Central.Failure.Answered.class, failure).status());
        assertEquals(List.of(), held());
    }

    @Test
    void aDownloadThatIsCutShortLeavesWhatWasThereAndNothingElse() throws Exception {
        Path old = FakeBackend.write(home.resolve("wasm-old.jar"), "wasm", OTHER, "old");
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("a", "wasm", HERE));
        repository.cut(WASM, "0.1.0", "cli");

        Central.Failure failure = failed("wasm");

        assertTrue(assertInstanceOf(Central.Failure.Unreachable.class, failure).reason()
                .startsWith("nothing arrived"), failure.toString());
        assertEquals(List.of(old.getFileName().toString()), held());
        assertInstanceOf(Backends.Absent.class, backends.find("wasm", HERE));
    }

    @Test
    void aJarThatDoesNotSayItIsTheBackendItWasReleasedAsIsNotInstalled() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("other-target", "native", HERE));

        assertEquals(new Central.Failure.NotTheBackend(
                        repository.uri().resolve(LocalRepository.path(WASM, "0.1.0", "cli", "jar")),
                        "wasm", HERE),
                failed("wasm"));
        assertEquals(List.of(), held());

        repository.metadata(WASM, "0.1.0", "0.2.0");
        repository.release(WASM, "0.2.0", "cli", HERE, jar("other-souther", "wasm", OTHER));
        assertInstanceOf(Central.Failure.NotTheBackend.class, failed("wasm"));
        assertEquals(List.of(), held());
    }

    @Test
    void aBackendBuiltForAnotherSoutherIsStoodBesideNotReplaced() throws Exception {
        Path old = FakeBackend.write(home.resolve("wasm.jar"), "wasm", OTHER, "old");
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("a", "wasm", HERE));

        assertInstanceOf(BackendFetch.Fetched.class, fetch("wasm"));

        assertEquals(List.of("wasm-" + HERE + ".jar", old.getFileName().toString()), held());
    }

    @Test
    void aPairThatIsThereByTheTimeItIsLookedForAgainIsNotFetched() throws Exception {
        Path there = FakeBackend.write(home.resolve("wasm.jar"), "wasm", HERE, "there");

        BackendFetch.Present present = assertInstanceOf(BackendFetch.Present.class,
                fetch("wasm"));

        assertEquals(there, present.backend().jar());
        assertEquals(List.of(), repository.asked());
    }

    @Test
    void fetchingAgainReplacesWhatTheLastFetchWroteAndRefusesWhatWasPutThereByHand()
            throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("first", "wasm", HERE));
        assertInstanceOf(BackendFetch.Fetched.class, fetch("wasm"));
        repository.metadata(WASM, "0.1.0", "0.1.1");
        repository.release(WASM, "0.1.1", "cli", HERE, jar("second", "wasm", HERE));

        BackendFetch.Fetched again = assertInstanceOf(BackendFetch.Fetched.class,
                BackendFetch.again(backends, central(), "wasm", HERE, release -> { }));

        assertEquals("0.1.1", again.release().version());
        assertEquals(List.of("wasm-" + HERE + ".jar"), held());

        Files.delete(again.backend().jar());
        Path byHand = FakeBackend.write(home.resolve("mine.jar"), "wasm", HERE, "mine");
        Backends.Refused refused = assertThrows(Backends.Refused.class,
                () -> BackendFetch.again(backends, central(), "wasm", HERE, release -> { }));
        assertEquals("cli.backend.fetch.held", refused.key());
        assertEquals(List.of(byHand.getFileName().toString()), held());
    }

    @Test
    void twoRunsFetchingTheSamePairFetchItOnce() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("a", "wasm", HERE));
        String jar = "/maven2/" + LocalRepository.path(WASM, "0.1.0", "cli", "jar");

        ExecutorService runs = Executors.newFixedThreadPool(4);
        List<Future<BackendFetch.Outcome>> outcomes = new ArrayList<>();
        try {
            for (int i = 0; i < 4; i++) {
                outcomes.add(runs.submit(() -> fetch("wasm")));
            }
            for (Future<BackendFetch.Outcome> outcome : outcomes) {
                BackendFetch.Outcome done = outcome.get();
                assertTrue(done instanceof BackendFetch.Fetched
                        || done instanceof BackendFetch.Present, done.toString());
            }
        } finally {
            runs.shutdownNow();
        }

        assertEquals(1, repository.asked().stream().filter(jar::equals).count(),
                repository.asked().toString());
        assertEquals(List.of("wasm-" + HERE + ".jar"), held());
    }

    @Test
    void releasesAreOrderedByTheirNumbersAndACandidateComesBeforeItsRelease() {
        List<String> ordered = List.of("0.1.0-rc1", "0.1.0-rc2", "0.1.0", "0.1.1", "0.2.0",
                "0.10.0", "1.0.0-alpha", "1.0.0-beta", "1.0.0-rc10", "1.0.0", "1.0.1");
        List<String> shuffled = new ArrayList<>(ordered.reversed());
        shuffled.sort(Central.RELEASE_ORDER);

        assertEquals(ordered, shuffled);
        assertTrue(Central.RELEASE_ORDER.compare("1.0", "1.0.0") != 0);
        assertTrue(Central.RELEASE_ORDER.compare("0.1.0-rc2", "0.1.0-rc10") < 0);
    }
}
