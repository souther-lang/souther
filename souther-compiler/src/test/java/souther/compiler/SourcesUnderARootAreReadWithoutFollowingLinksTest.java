package souther.compiler;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.compiler.CompilationSources.SourceFile;
import souther.compiler.io.ConfinementException;
import souther.compiler.meta.ModulePath;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/** What is found under a root the caller named is not the caller's own, and is not followed out of it. */
class SourcesUnderARootAreReadWithoutFollowingLinksTest {

    private static void link(Path link, Path target) throws IOException {
        try {
            Files.createSymbolicLink(link, target);
        } catch (UnsupportedOperationException | IOException e) {
            assumeTrue(false, "symbolic links cannot be made here: " + e);
        }
    }

    @Test
    void everySouUnderTheRootIsReadInPathOrder(@TempDir Path dir) throws IOException {
        Files.writeString(dir.resolve("b.sou"), "b");
        Files.createDirectories(dir.resolve("a"));
        Files.writeString(dir.resolve("a/x.sou"), "x");
        Files.writeString(dir.resolve("a-b.sou"), "ab");
        Files.writeString(dir.resolve("readme.md"), "not a source");

        List<SourceFile> read = CompilationSources.readTree(dir);

        List<Path> expected = Stream.of("a/x.sou", "a-b.sou", "b.sou").map(Path::of).sorted().toList();
        assertEquals(expected, read.stream().map(s -> dir.relativize(Path.of(s.path()))).toList(),
                "in the order Path sorts them, which is the order a compile has always been given them in");
    }

    @Test
    void aSouThatIsALinkIsRefused(@TempDir Path dir) throws IOException {
        Path elsewhere = Files.writeString(dir.resolve("secret.txt"), "not a source");
        Path root = Files.createDirectories(dir.resolve("root"));
        link(root.resolve("secret.sou"), elsewhere);

        assertThrows(ConfinementException.class, () -> CompilationSources.readTree(root));
    }

    @Test
    void aDirectoryThatIsALinkIsNotWalked(@TempDir Path dir) throws IOException {
        Path outside = Files.createDirectories(dir.resolve("outside"));
        Files.writeString(outside.resolve("other.sou"), "other");
        Path root = Files.createDirectories(dir.resolve("root"));
        Files.writeString(root.resolve("mine.sou"), "mine");
        link(root.resolve("dir"), outside);

        assertEquals(1, CompilationSources.readTree(root).size());
    }

    @Test
    void aClassOutputIsReadOnlyThroughRealDirectories(@TempDir Path dir) throws IOException {
        Path outside = Files.createDirectories(dir.resolve("outside"));
        Files.write(outside.resolve("Secret.class"), new byte[]{1});
        Path classes = Files.createDirectories(dir.resolve("classes"));
        Files.createDirectories(classes.resolve("real"));
        Files.write(classes.resolve("real/Kept.class"), new byte[]{2});
        link(classes.resolve("shared"), outside);
        ModulePath path = ModulePath.ofClassPath(List.of(classes));

        assertNotNull(path.bytes("real.Kept"));
        assertNull(path.bytes("shared.Secret"), "a class behind a link in the output is not read");
        assertNull(path.bytes("..Escape"), "and a name that is not a name reads as a class that is not there");
    }
}
