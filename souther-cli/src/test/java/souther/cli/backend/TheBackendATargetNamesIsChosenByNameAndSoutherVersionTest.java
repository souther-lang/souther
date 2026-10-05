package souther.cli.backend;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A backend is identified by the target it answers to and the Souther it was built against. What
 * this holds is which of the jars in the directories is the one a target means, and what is said
 * where none is.
 */
class TheBackendATargetNamesIsChosenByNameAndSoutherVersionTest {

    private static final String HERE = "9.9.9";
    private static final String OLDER = "9.9.8";

    private static Backends.Refused refused(Backends backends, String target) {
        return assertThrows(Backends.Refused.class, () -> backends.choose(target, HERE));
    }

    @Test
    void theJarBuiltAgainstThisSoutherIsChosenBesideOthersOfTheSameTarget(@TempDir Path dir)
            throws Exception {
        FakeBackend.write(dir.resolve("wasm-old.jar"), "wasm", OLDER, "old");
        Path here = FakeBackend.write(dir.resolve("wasm-here.jar"), "wasm", HERE, "here");
        FakeBackend.write(dir.resolve("native-here.jar"), "native", HERE, "native");

        Backends.Backend chosen = new Backends(List.of(dir)).choose("wasm", HERE);

        assertEquals(new Backends.Backend("wasm", HERE, here), chosen);
    }

    @Test
    void theFirstDirectoryHoldingTheTargetDecidesEvenWhenItsJarIsForAnotherSouther(
            @TempDir Path home, @TempDir Path packaged) throws Exception {
        FakeBackend.write(home.resolve("wasm.jar"), "wasm", OLDER, "stale");
        FakeBackend.write(packaged.resolve("wasm.jar"), "wasm", HERE, "packaged");

        Backends.Refused said = refused(new Backends(List.of(home, packaged)), "wasm");

        assertEquals("cli.backend.version", said.key());
        assertArrayEquals(new Object[] {"wasm", OLDER, HERE}, said.arguments());
    }

    @Test
    void aTargetTheFirstDirectoryDoesNotHoldIsFoundInTheNext(@TempDir Path home,
                                                             @TempDir Path packaged)
            throws Exception {
        FakeBackend.write(home.resolve("native.jar"), "native", HERE, "home");
        Path wasm = FakeBackend.write(packaged.resolve("wasm.jar"), "wasm", HERE, "packaged");

        Backends.Backend chosen = new Backends(List.of(home, packaged)).choose("wasm", HERE);

        assertEquals(wasm, chosen.jar());
    }

    @Test
    void theFirstDirectoryWinsWhereBothHoldTheSamePair(@TempDir Path home,
                                                       @TempDir Path packaged)
            throws Exception {
        Path development = FakeBackend.write(home.resolve("wasm.jar"), "wasm", HERE, "dev");
        FakeBackend.write(packaged.resolve("wasm.jar"), "wasm", HERE, "packaged");

        Backends.Backend chosen = new Backends(List.of(home, packaged)).choose("wasm", HERE);

        assertEquals(development, chosen.jar());
    }

    @Test
    void twoJarsOfOnePairInOneDirectoryAreRefused(@TempDir Path dir) throws Exception {
        FakeBackend.write(dir.resolve("a.jar"), "wasm", HERE, "a");
        FakeBackend.write(dir.resolve("b.jar"), "wasm", HERE, "b");

        Backends.Refused said = refused(new Backends(List.of(dir)), "wasm");

        assertEquals("cli.backend.duplicate", said.key());
    }

    @Test
    void anUnknownTargetNamesWhatIsInstalled(@TempDir Path dir) throws Exception {
        FakeBackend.write(dir.resolve("native.jar"), "native", HERE, "n");
        FakeBackend.write(dir.resolve("wasm.jar"), "wasm", OLDER, "w");

        Backends.Refused said = refused(new Backends(List.of(dir)), "llvm");

        assertEquals("cli.backend.unknown", said.key());
        assertArrayEquals(new Object[] {"llvm", "native, wasm"}, said.arguments());
    }

    @Test
    void anUnknownTargetWithNoBackendAtAllSaysSo(@TempDir Path dir) {
        assertEquals("cli.backend.unknown.none", refused(new Backends(List.of(dir)), "wasm").key());
        assertEquals("cli.backend.unknown.none",
                refused(new Backends(List.of(dir.resolve("absent"))), "wasm").key());
        assertEquals("cli.backend.unknown.none", refused(new Backends(List.of()), "wasm").key());
    }

    @Test
    void aJarWithNoDescriptorOrAnythingButTheTwoKeysIsRefused(@TempDir Path dir)
            throws Exception {
        for (String descriptor : new String[] {
                null,
                "name=wasm\n",
                "souther.version=" + HERE + "\n",
                "name=wasm\nsouther.version=" + HERE + "\nrelease=1\n",
                "name=\nsouther.version=" + HERE + "\n",
                "name=wasm\nsouther.version=" + HERE + " \n",
                "name=wasm \nsouther.version=" + HERE + "\n",
                "name=wasm\nsouther.version=" + HERE + " x\n"}) {
            Path jar = FakeBackend.writeWithDescriptor(dir.resolve("b.jar"), descriptor);

            Backends.Refused said = refused(new Backends(List.of(dir)), "wasm");

            assertEquals("cli.backend.descriptor", said.key(), String.valueOf(descriptor));
            assertArrayEquals(new Object[] {jar}, said.arguments());
        }
    }

    @Test
    void aFileThatIsNotAJarIsNotOneEither(@TempDir Path dir) throws IOException {
        Path notAJar = Files.writeString(dir.resolve("b.jar"), "not an archive");

        Backends.Refused said = refused(new Backends(List.of(dir)), "wasm");

        assertEquals("cli.backend.descriptor", said.key());
        assertArrayEquals(new Object[] {notAJar}, said.arguments());
    }

    @Test
    void aLinkToAJarThatIsNotThereIsRefused(@TempDir Path dir) throws IOException {
        Path link = Files.createSymbolicLink(dir.resolve("wasm.jar"), dir.resolve("gone.jar"));

        Backends.Refused said = refused(new Backends(List.of(dir)), "wasm");

        assertEquals("cli.backend.link", said.key());
        assertArrayEquals(new Object[] {link}, said.arguments());
    }

    @Test
    void aDirectoryThatIsALinkToNothingOrAFileIsRefusedAndAbsentIsNot(@TempDir Path dir)
            throws IOException {
        Path link = Files.createSymbolicLink(dir.resolve("dangling"), dir.resolve("gone"));
        Path file = Files.writeString(dir.resolve("file"), "x");

        for (Path held : List.of(link, file)) {
            Backends.Refused said = refused(new Backends(List.of(held)), "wasm");

            assertEquals("cli.backend.directory", said.key());
            assertArrayEquals(new Object[] {held, "not a directory"}, said.arguments());
        }
        assertEquals("cli.backend.unknown.none",
                refused(new Backends(List.of(dir.resolve("absent"))), "wasm").key());
    }

    @Test
    void aLinkToAJarIsABackend(@TempDir Path dir, @TempDir Path elsewhere) throws Exception {
        Path jar = FakeBackend.write(elsewhere.resolve("real.jar"), "wasm", HERE, "linked");
        Path link = Files.createSymbolicLink(dir.resolve("wasm.jar"), jar);

        assertEquals(link, new Backends(List.of(dir)).choose("wasm", HERE).jar());
    }

    @Test
    void whatIsNotNamedAJarIsNotLookedAt(@TempDir Path dir) throws Exception {
        Files.writeString(dir.resolve("README"), "not a backend");
        Path wasm = FakeBackend.write(dir.resolve("wasm.jar"), "wasm", HERE, "w");

        assertEquals(wasm, new Backends(List.of(dir)).choose("wasm", HERE).jar());
    }
}
