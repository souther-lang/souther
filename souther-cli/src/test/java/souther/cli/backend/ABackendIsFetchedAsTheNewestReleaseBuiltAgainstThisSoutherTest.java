package souther.cli.backend;

import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.net.URI;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFileAttributeView;
import java.nio.file.attribute.PosixFilePermissions;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.stream.Stream;

import static java.nio.charset.StandardCharsets.ISO_8859_1;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeFalse;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

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

    private Central central() {
        return Central.at(repository.uri(), Central.Patience.USUAL);
    }

    private Central.Failure failedWaiting(Duration answer, Duration stall) throws Exception {
        return assertInstanceOf(BackendFetch.Failed.class, BackendFetch.whereAbsent(backends,
                Central.at(repository.uri(), new Central.Patience(answer, stall)), "wasm", HERE,
                release -> { })).failure();
    }

    private BackendFetch.Supplied fetch(String target) throws Exception {
        return BackendFetch.whereAbsent(backends, central(), target, HERE,
                release -> { });
    }

    private BackendFetch.Refreshed again(String target) throws Exception {
        return BackendFetch.again(backends, central(), target, HERE, release -> { });
    }

    private Central.Failure failed(String target) throws Exception {
        return assertInstanceOf(BackendFetch.Failed.class, fetch(target)).failure();
    }

    /** What the directory holds besides the lock and the records of what was fetched, by name. */
    private List<String> held() throws IOException {
        try (Stream<Path> listed = Files.list(home)) {
            return listed.map(path -> path.getFileName().toString())
                    .filter(name -> !name.equals(".fetching.lock") && !name.endsWith(".fetched"))
                    .sorted().toList();
        }
    }

    private long askedFor(String path) {
        return repository.asked().stream().filter(("/maven2/" + path)::equals).count();
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
    void aReleaseWhosePomCannotBeReadIsPassedOverAndNamedWhereNothingElseIsFound()
            throws Exception {
        repository.metadata(WASM, "0.1.0", "0.2.0", "0.3.0", "0.4.0", "0.5.0", "0.6.0",
                "0.7.0{x}");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("oldest", "wasm", HERE));
        repository.put(LocalRepository.path(WASM, "0.2.0", null, "pom"),
                "<project><artifactId>x</artifactId></project>");
        repository.pom(WASM, "0.3.0",
                LocalRepository.builtAgainst(WASM, "0.3.0", "${project.version}"));
        repository.pom(WASM, "0.4.0", LocalRepository.inheriting(WASM, "0.4.0",
                "souther-native-parent", "${revision}"));
        repository.put(LocalRepository.path(WASM, "0.5.0", null, "pom"), "<project><prop");
        // 0.6.0 is listed and has no pom at all.

        BackendFetch.Fetched fetched = assertInstanceOf(BackendFetch.Fetched.class,
                fetch("wasm"));

        assertEquals("0.1.0", fetched.release().version());

        repository.release(WASM, "0.1.0", "cli", OTHER, jar("oldest", "wasm", OTHER));
        Files.delete(fetched.backend().jar());
        assertEquals(new Central.Failure.NoneBuilt(HERE,
                        List.of("0.1.0", "0.2.0", "0.3.0", "0.4.0", "0.5.0", "0.6.0"),
                        List.of("0.6.0", "0.5.0", "0.4.0", "0.3.0", "0.2.0"),
                        List.of("0.7.0{x}")),
                failed("wasm"));
    }

    @Test
    void releasesAreAskedForSeveralAtATimeAndTheNewestBuiltAgainstThisSoutherIsTaken()
            throws Exception {
        List<String> versions = new ArrayList<>();
        for (int i = 0; i < 16; i++) {
            versions.add("0." + i + ".0");
            repository.pom(WASM, "0." + i + ".0", LocalRepository.builtAgainst(WASM,
                    "0." + i + ".0", i == 3 || i == 1 ? HERE : OTHER));
        }
        repository.metadata(WASM, versions.toArray(String[]::new));
        repository.jar(WASM, "0.3.0", "cli", jar("third", "wasm", HERE));
        repository.slowPoms(300);

        long started = System.nanoTime();
        BackendFetch.Fetched fetched = assertInstanceOf(BackendFetch.Fetched.class,
                fetch("wasm"));
        Duration took = Duration.ofNanos(System.nanoTime() - started);

        assertEquals("0.3.0", fetched.release().version());
        // Thirteen poms one at a time would be thirteen waits; two windows of them are two.
        assertTrue(took.compareTo(Duration.ofMillis(300L * 13 / 2)) < 0, took.toString());
    }

    @Test
    void aRedirectIsFollowedOnlyToWhereARepositoryMayBeReached() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("moved", "wasm", HERE));
        String jar = LocalRepository.path(WASM, "0.1.0", "cli", "jar");
        repository.jar("moved", "0.1.0", null, work.resolve("served/moved.jar"));
        repository.redirect(jar, "/maven2/" + LocalRepository.path("moved", "0.1.0", null, "jar"));

        assertInstanceOf(BackendFetch.Fetched.class, fetch("wasm"));

        Files.delete(home.resolve("wasm-" + HERE + ".jar"));
        repository.redirect(jar, "http://repository.example/elsewhere.jar");
        Central.Failure failure = failed("wasm");

        assertEquals(new Central.Failure.Redirected(repository.uri().resolve(jar),
                URI.create("http://repository.example/elsewhere.jar")), failure);
        assertEquals(List.of(), held());
    }

    @Test
    void aTargetNothingCanBeAskedAboutTouchesNoDirectory() throws Exception {
        assertEquals(new Central.Failure.Unregistered("llvm"), failed("llvm"));

        assertTrue(Files.notExists(home), "the directory was made for a fetch that asked nothing");
    }

    @Test
    void noReleaseBuiltAgainstThisSoutherNamesTheReleasesThereAre() throws Exception {
        repository.metadata(WASM, "0.2.0", "0.1.0");
        repository.release(WASM, "0.1.0", "cli", OTHER, jar("a", "wasm", OTHER));
        repository.release(WASM, "0.2.0", "cli", OTHER, jar("b", "wasm", OTHER));

        assertEquals(new Central.Failure.NoneBuilt(HERE, List.of("0.1.0", "0.2.0"), List.of(),
                List.of()), failed("wasm"));
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

        // A tenth of a second is short of what a download would be given, and long enough here:
        // this one has stopped, so taking it to have stopped sooner changes nothing about it.
        Central.Failure failure = failedWaiting(Duration.ofSeconds(60), Duration.ofMillis(100));

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
    void fetchingAgainTheReleaseFetchedBeforeDownloadsNothing() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("first", "wasm", HERE));
        String jar = LocalRepository.path(WASM, "0.1.0", "cli", "jar");
        BackendFetch.Fetched first = assertInstanceOf(BackendFetch.Fetched.class, again("wasm"));

        BackendFetch.Current current = assertInstanceOf(BackendFetch.Current.class,
                again("wasm"));

        assertEquals(first.backend(), current.backend());
        assertEquals(1, askedFor(jar));

        // What a run ended between moving the jar and saying which release it is leaves.
        Path record = home.resolve(".wasm-" + HERE + ".jar.fetched");
        Files.writeString(record, "");
        assertInstanceOf(BackendFetch.Fetched.class, again("wasm"));
        assertEquals(2, askedFor(jar));

        Files.delete(record);
        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> again("wasm"));
        assertEquals("cli.backend.fetch.held", refused.key());
        assertEquals(2, askedFor(jar));
    }

    @Test
    void aJarPutByHandUnderTheNameAFetchWritesIsRefusedBeforeAnythingIsDownloaded()
            throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("served", "wasm", HERE));
        Path byHand = FakeBackend.write(home.resolve("wasm-" + HERE + ".jar"), "wasm", OTHER,
                "mine");

        Backends.Refused refused = assertThrows(Backends.Refused.class, () -> again("wasm"));

        assertEquals("cli.backend.fetch.held", refused.key());
        assertEquals(0, askedFor(LocalRepository.path(WASM, "0.1.0", "cli", "jar")));
        assertEquals(OTHER, Backends.describe(byHand).southerVersion());
    }

    @Test
    void twoRunsFetchingTheSamePairFetchItOnce() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("a", "wasm", HERE));
        String jar = "/maven2/" + LocalRepository.path(WASM, "0.1.0", "cli", "jar");

        ExecutorService runs = Executors.newFixedThreadPool(4);
        List<Future<BackendFetch.Supplied>> outcomes = new ArrayList<>();
        try {
            for (int i = 0; i < 4; i++) {
                outcomes.add(runs.submit(() -> fetch("wasm")));
            }
            for (Future<BackendFetch.Supplied> outcome : outcomes) {
                BackendFetch.Supplied done = outcome.get();
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
    void aJarThatKeepsArrivingIsWaitedForPastTheTimeASmallFileHas() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("slow", "wasm", HERE));
        repository.trickle(LocalRepository.path(WASM, "0.1.0", "cli", "jar"), 8, 150);

        BackendFetch.Fetched fetched = assertInstanceOf(BackendFetch.Fetched.class,
                BackendFetch.whereAbsent(backends, Central.at(repository.uri(),
                        new Central.Patience(Duration.ofMillis(400), Duration.ofMillis(600))),
                        "wasm", HERE, release -> { }));

        assertEquals(home.resolve("wasm-" + HERE + ".jar"), fetched.backend().jar());
    }

    @Test
    void aJarWhoseAnswerNeverBeginsIsGivenUpOnceAnAnswerShouldHaveBegun() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("late", "wasm", HERE));
        repository.holdBack(LocalRepository.path(WASM, "0.1.0", "cli", "jar"), 5000);

        Central.Failure failure = failedWaiting(Duration.ofMillis(300), Duration.ofSeconds(60));

        assertTrue(assertInstanceOf(Central.Failure.Unreachable.class, failure).reason()
                .startsWith("no answer began"), failure.toString());
        assertEquals(List.of(), held());
    }

    @Test
    void aJarThatBeginsAndSendsNothingIsGivenUpAStallLaterAndNotTwo() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("silent", "wasm", HERE));
        repository.silence(LocalRepository.path(WASM, "0.1.0", "cli", "jar"));
        Duration stall = Duration.ofSeconds(1);

        long started = System.nanoTime();
        Central.Failure failure = failedWaiting(Duration.ofSeconds(60), stall);
        Duration took = Duration.ofNanos(System.nanoTime() - started);

        assertTrue(assertInstanceOf(Central.Failure.Unreachable.class, failure).reason()
                .startsWith("nothing arrived"), failure.toString());
        // A stall and its looking come to a stall and two fifths at most; ending a stall late
        // would be two. What lies between leaves a loaded machine room on either side.
        assertTrue(took.compareTo(stall) >= 0 && took.compareTo(stall.multipliedBy(17)
                .dividedBy(10)) < 0, took.toString());
    }

    @Test
    void metadataWhoseBodyStopsAfterItBeganIsGivenUpAtTheDeadlineOnEveryJdk() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.silence("org/souther-lang/" + WASM + "/maven-metadata.xml");

        long started = System.nanoTime();
        Central.Failure failure = failedWaiting(Duration.ofMillis(400), Duration.ofSeconds(60));
        Duration took = Duration.ofNanos(System.nanoTime() - started);

        assertTrue(assertInstanceOf(Central.Failure.Unreachable.class, failure).reason()
                .startsWith("it did not arrive"), failure.toString());
        assertTrue(took.compareTo(Duration.ofSeconds(5)) < 0, took.toString());
    }

    @Test
    void aJarReachedThroughARedirectWithALongBodyIsTheJarAndNothingOfTheBody() throws Exception {
        repository.metadata(WASM, "0.1.0");
        Path served = jar("moved", "wasm", HERE);
        repository.release(WASM, "0.1.0", "cli", HERE, served);
        repository.jar("moved", "0.1.0", null, served);
        repository.redirect(LocalRepository.path(WASM, "0.1.0", "cli", "jar"),
                "/maven2/" + LocalRepository.path("moved", "0.1.0", null, "jar"),
                (int) Files.size(served) * 4);

        BackendFetch.Fetched fetched = assertInstanceOf(BackendFetch.Fetched.class,
                fetch("wasm"));

        assertEquals(Files.size(served), Files.size(fetched.backend().jar()));
    }

    @Test
    void aRedirectToAnAddressWithNoHostIsNotFollowed() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("a", "wasm", HERE));
        String jar = LocalRepository.path(WASM, "0.1.0", "cli", "jar");

        for (String location : List.of("https:/missing-host", "https:opaque", "https:///x.jar")) {
            repository.redirect(jar, location);

            assertInstanceOf(Central.Failure.Redirected.class, failed("wasm"), location);
        }
        assertEquals(List.of(), held());
    }

    @Test
    void aDirectoryThatCannotBeWrittenIsSaidAsSuchAndNotAsTheRepository() throws Exception {
        repository.metadata(WASM, "0.1.0");
        repository.release(WASM, "0.1.0", "cli", HERE, jar("a", "wasm", HERE));
        Files.createDirectories(home);
        assumeTrue(Files.getFileStore(home).supportsFileAttributeView(PosixFileAttributeView.class));
        Files.setPosixFilePermissions(home, PosixFilePermissions.fromString("r-xr-xr-x"));
        try {
            assumeFalse(Files.isWritable(home), "this user writes where permissions say not");

            Central.Failure failure = failed("wasm");

            assertEquals(home, assertInstanceOf(Central.Failure.Unwritable.class, failure)
                    .directory());
        } finally {
            Files.setPosixFilePermissions(home, PosixFilePermissions.fromString("rwxr-xr-x"));
        }
    }

    @Test
    void aProxyThisCannotSendThroughIsRefusedForWhatItIs() {
        for (Map.Entry<String, Central.Failure.Misread> named : Map.of(
                "http://alice:secret@proxy:8080", Central.Failure.Misread.CREDENTIALS,
                "https://proxy:8443", Central.Failure.Misread.SCHEME,
                "socks5://proxy:1080", Central.Failure.Misread.SCHEME,
                "http://", Central.Failure.Misread.NOT_AN_ADDRESS).entrySet()) {
            Configured configured = Repository.configured(Map.of("HTTPS_PROXY", named.getKey()));

            assertEquals(named.getValue(), assertInstanceOf(Configured.Unusable.class, configured)
                    .why().why(), named.getKey());
        }
        assertInstanceOf(Repository.class,
                Repository.configured(Map.of("HTTPS_PROXY", "proxy:3128")));
        assertInstanceOf(Repository.class,
                Repository.configured(Map.of("HTTPS_PROXY", "http://alice:secret@proxy:8080",
                        "NO_PROXY", "repo.maven.apache.org")));
    }

    @Test
    void noProxyNamesAHostADomainOrEveryHost() {
        assertTrue(Repository.bypassed("nexus.corp", "localhost, nexus.corp"));
        assertTrue(Repository.bypassed("repo.nexus.corp", "nexus.corp"));
        assertTrue(Repository.bypassed("repo.nexus.corp", ".nexus.corp"));
        assertTrue(Repository.bypassed("NEXUS.corp", "nexus.CORP"));
        assertTrue(Repository.bypassed("repo.maven.apache.org", "*"));
        assertFalse(Repository.bypassed("repo.maven.apache.org", "nexus.corp,,apache"));
        assertFalse(Repository.bypassed("notnexus.corp", "nexus.corp"));
        assertFalse(Repository.bypassed("repo.maven.apache.org", ""));
    }

    @Test
    void onlyHttpsOrPlainHttpOnTheLoopbackMayBeAsked() {
        assertTrue(Repository.admits(URI.create("https://repo.example/x")));
        assertTrue(Repository.admits(URI.create("http://127.0.0.1:8080/x")));
        assertTrue(Repository.admits(URI.create("http://localhost/x")));
        assertFalse(Repository.admits(URI.create("http://repo.example/x")));
        assertFalse(Repository.admits(URI.create("ftp://repo.example/x")));
        assertFalse(Repository.admits(URI.create("file:///tmp/x.jar")));
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
