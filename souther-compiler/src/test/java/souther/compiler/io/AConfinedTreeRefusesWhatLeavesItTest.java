package souther.compiler.io;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertArrayEquals;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * A name that came from somewhere other than the caller reaches a file only as far as the tree
 * agrees. What is refused is refused on what is on disk, not on the text of the name: a link in the
 * middle of a name that reads as perfectly inside the tree is what a check of the text lets through.
 */
class AConfinedTreeRefusesWhatLeavesItTest {

    private static void link(Path link, Path target) throws IOException {
        try {
            Files.createSymbolicLink(link, target);
        } catch (UnsupportedOperationException | IOException e) {
            assumeTrue(false, "symbolic links cannot be made here: " + e);
        }
    }

    @Test
    void aNameThatIsNotAPlainRelativePathIsRefused(@TempDir Path dir) {
        ConfinedTree tree = ConfinedTree.at(dir);

        for (String name : new String[]{"", "..", "../x", "a/../../x", "/etc/passwd", "a/./b", "a\0b"}) {
            assertThrows(ConfinementException.class, () -> tree.resolve(name), "`" + name + "`");
        }
    }

    @Test
    void aFileIsReadAndWrittenUnderTheRootAndItsDirectoriesAreMade(@TempDir Path dir) throws IOException {
        ConfinedTree tree = ConfinedTree.at(dir);

        tree.write("a/b/c.txt", "hello".getBytes(StandardCharsets.UTF_8));

        assertEquals("hello", tree.readString("a/b/c.txt", 100));
        assertEquals(dir.resolve("a/b/c.txt"), tree.resolve("a/b/c.txt"));
    }

    @Test
    void aDirectoryOnTheWayThatIsALinkIsNeitherReadNorWrittenNorDeletedThrough(@TempDir Path dir)
            throws IOException {
        Path outside = Files.createDirectories(dir.resolve("outside"));
        Path victim = Files.writeString(outside.resolve("victim.txt"), "keep");
        Path root = Files.createDirectories(dir.resolve("root"));
        link(root.resolve("escape"), outside);
        ConfinedTree tree = ConfinedTree.at(root);

        assertThrows(ConfinementException.class, () -> tree.read("escape/victim.txt", 100));
        assertThrows(ConfinementException.class, () -> tree.write("escape/new.txt", new byte[]{1}));
        assertThrows(ConfinementException.class, () -> tree.deleteIfExists("escape/victim.txt"));

        assertEquals("keep", Files.readString(victim));
        assertFalse(Files.exists(outside.resolve("new.txt")));
    }

    @Test
    void aFileThatIsALinkIsNotOpenedAndNotWrittenThrough(@TempDir Path dir) throws IOException {
        Path elsewhere = Files.writeString(dir.resolve("elsewhere.txt"), "keep");
        Path root = Files.createDirectories(dir.resolve("root"));
        link(root.resolve("file.txt"), elsewhere);
        ConfinedTree tree = ConfinedTree.at(root);

        assertThrows(ConfinementException.class, () -> tree.read("file.txt", 100));
        assertThrows(ConfinementException.class, () -> tree.write("file.txt", new byte[]{1}));

        assertEquals("keep", Files.readString(elsewhere));
        assertFalse(tree.isRegularFile("file.txt"), "a link reads as not being a file");
    }

    @Test
    void aRootThatIsItselfALinkIsTheCallersOwnAndIsUsed(@TempDir Path dir) throws IOException {
        Path real = Files.createDirectories(dir.resolve("real"));
        Files.writeString(real.resolve("a.txt"), "a");
        Path alias = dir.resolve("alias");
        link(alias, real);
        ConfinedTree tree = ConfinedTree.at(alias);

        assertEquals("a", tree.readString("a.txt", 10));
    }

    @Test
    void aFileLargerThanTheLimitIsNotHeld(@TempDir Path dir) throws IOException {
        Files.write(dir.resolve("big.bin"), new byte[100]);

        assertThrows(LimitExceededException.class, () -> ConfinedTree.at(dir).read("big.bin", 99));
        assertEquals(100, ConfinedTree.at(dir).read("big.bin", 100).length);
    }

    @Test
    void emptyDirectoriesAreRemovedUpToButNotIncludingTheRoot(@TempDir Path dir) throws IOException {
        ConfinedTree tree = ConfinedTree.at(dir);
        tree.write("a/b/c.txt", new byte[]{1});
        tree.write("a/keep.txt", new byte[]{1});

        tree.deleteIfExists("a/b/c.txt");
        tree.deleteEmptyParents("a/b/c.txt");

        assertFalse(Files.exists(dir.resolve("a/b")), "the emptied directory goes");
        assertTrue(Files.exists(dir.resolve("a")), "the one still holding a file stays");
        assertTrue(Files.exists(dir), "and never the root");
    }

    @Test
    void aWalkReportsLinksWithoutGoingThroughThemAndStopsAtTheLimit(@TempDir Path dir) throws IOException {
        Path outside = Files.createDirectories(dir.resolve("outside"));
        Files.writeString(outside.resolve("secret.sou"), "secret");
        Path root = Files.createDirectories(dir.resolve("root"));
        Files.writeString(root.resolve("a.sou"), "a");
        link(root.resolve("dir"), outside);
        link(root.resolve("b.sou"), outside.resolve("secret.sou"));
        List<String> files = new ArrayList<>();
        List<String> links = new ArrayList<>();
        ConfinedTree tree = ConfinedTree.at(root);

        boolean complete = tree.walk(1_000, new ConfinedTree.Entries() {
            @Override
            public void regularFile(String relative) {
                files.add(relative);
            }

            @Override
            public void link(String relative) {
                links.add(relative);
            }
        });

        assertTrue(complete);
        assertEquals(List.of("a.sou"), files);
        assertEquals(List.of("b.sou", "dir"), links.stream().sorted().toList());
        assertFalse(tree.walk(1, new ConfinedTree.Entries() {
            @Override
            public void regularFile(String relative) {}
        }), "a walk that reaches the limit says it did not finish");
    }

    @Test
    void aStreamIsReadUpToTheLimitAndNoFurther() throws IOException {
        assertArrayEquals(new byte[]{1, 2, 3}, BoundedRead.bytes(new ByteArrayInputStream(new byte[]{1, 2, 3}), 3));
        assertThrows(LimitExceededException.class,
                () -> BoundedRead.bytes(new ByteArrayInputStream(new byte[]{1, 2, 3}), 2));
    }
}
