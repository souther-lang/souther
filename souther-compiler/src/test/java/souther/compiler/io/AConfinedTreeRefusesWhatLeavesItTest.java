package souther.compiler.io;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.NoSuchFileException;
import java.nio.file.NotDirectoryException;
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

        tree.walk(1_000, entry -> {
            switch (entry) {
                case ConfinedTree.Reached.RegularFile file -> files.add(file.relative());
                case ConfinedTree.Reached.Link link -> links.add(link.relative());
                case ConfinedTree.Reached.Directory _, ConfinedTree.Reached.Other _ -> {
                }
            }
        });

        assertEquals(List.of("a.sou"), files);
        assertEquals(List.of("b.sou", "dir"), links.stream().sorted().toList());
        assertThrows(LimitExceededException.class, () -> tree.walk(1, new ConfinedTree.Entries() {
            @Override
            public void reached(ConfinedTree.Reached entry) {}
        }), "a walk that reaches the limit says it did not finish");
    }

    @Test
    void aWalkThatReachesTheLimitEndsWithWhatItSawWhereTheCallerTakesPartOfATree(@TempDir Path dir)
            throws IOException {
        Files.writeString(dir.resolve("a.sou"), "a");
        Files.writeString(dir.resolve("b.sou"), "b");
        List<String> files = new ArrayList<>();
        List<LimitExceededException> reached = new ArrayList<>();

        ConfinedTree.at(dir).walk(2, new ConfinedTree.Entries() {
            @Override
            public void reached(ConfinedTree.Reached entry) {
                if (entry instanceof ConfinedTree.Reached.RegularFile) {
                    files.add(entry.relative());
                }
            }

            @Override
            public void limitReached(LimitExceededException cause) {
                reached.add(cause);
            }
        });

        // The root and one file are the two entries allowed.
        assertEquals(1, files.size());
        assertEquals(1, reached.size());
        assertTrue(reached.getFirst().getMessage().contains(dir.toString()));
    }

    @Test
    void aDirectoryTheWalkCannotOpenIsReportedRatherThanPassedOver(@TempDir Path dir)
            throws IOException {
        Files.writeString(dir.resolve("visible.sou"), "visible");
        Path closed = Files.createDirectories(dir.resolve("private"));
        Files.writeString(closed.resolve("hidden.sou"), "hidden");
        try (ClosedDirectory _ = ClosedDirectory.shut(closed)) {
            ConfinedTree tree = ConfinedTree.at(dir);

            IOException thrown = assertThrows(IOException.class, () -> tree.walk(1_000,
                    new ConfinedTree.Entries() {
                        @Override
                        public void reached(ConfinedTree.Reached entry) {}
                    }));
            assertTrue(thrown.getMessage().contains("private"), thrown.getMessage());

            List<String> unreadable = new ArrayList<>();
            List<String> files = new ArrayList<>();
            tree.walk(1_000, new ConfinedTree.Entries() {
                @Override
                public void reached(ConfinedTree.Reached entry) {
                    if (entry instanceof ConfinedTree.Reached.RegularFile) {
                        files.add(entry.relative());
                    }
                }

                @Override
                public void unreadable(String relative, IOException cause) {
                    unreadable.add(relative);
                }
            });
            assertEquals(List.of("private"), unreadable);
            assertEquals(List.of("visible.sou"), files);
        }
    }

    @Test
    void aDirectoryReadPartWayIsReportedAsNotAllSeen(@TempDir Path dir) throws IOException {
        // A directory that opened and then failed part way through its entries reaches the walk
        // after what it holds, not before; the file system cannot be made to do that on demand, so
        // the walk is handed it as Files.walkFileTree would hand it.
        List<String> unreadable = new ArrayList<>();
        ConfinedTree.Walker walker = new ConfinedTree.Walker(dir, 1_000, new ConfinedTree.Entries() {
            @Override
            public void reached(ConfinedTree.Reached entry) {}

            @Override
            public void unreadable(String relative, IOException cause) {
                unreadable.add(relative);
            }
        });

        walker.postVisitDirectory(dir.resolve("a").resolve("b"), new IOException("gone"));
        walker.postVisitDirectory(dir.resolve("c"), null);

        assertEquals(List.of("a/b"), unreadable);
        ConfinedTree.Walker strict = new ConfinedTree.Walker(dir, 1_000, new ConfinedTree.Entries() {
            @Override
            public void reached(ConfinedTree.Reached entry) {}
        });
        assertThrows(IOException.class,
                () -> strict.postVisitDirectory(dir.resolve("a"), new IOException("gone")));
    }

    @Test
    void anEntryThatCouldNotBeReadIsCountedAgainstTheLimit(@TempDir Path dir) throws IOException {
        List<ClosedDirectory> closed = new ArrayList<>();
        try {
            for (String name : List.of("a", "b", "c", "d")) {
                closed.add(ClosedDirectory.shut(Files.createDirectories(dir.resolve(name))));
            }
            List<String> unreadable = new ArrayList<>();
            int[] visited = {0};
            List<LimitExceededException> reached = new ArrayList<>();

            ConfinedTree.at(dir).walk(3, new ConfinedTree.Entries() {
                @Override
                public void visited() {
                    visited[0]++;
                }

                @Override
                public void reached(ConfinedTree.Reached entry) {}

                @Override
                public void unreadable(String relative, IOException cause) {
                    unreadable.add(relative);
                }

                @Override
                public void limitReached(LimitExceededException cause) {
                    reached.add(cause);
                }
            });

            // The root and two of the four, and then the third is one too many.
            assertEquals(2, unreadable.size());
            assertEquals(4, visited[0]);
            assertEquals(1, reached.size());
        } finally {
            for (ClosedDirectory each : closed) {
                each.close();
            }
        }
    }

    @Test
    void aRootThatIsAFileIsNotATree(@TempDir Path dir) throws IOException {
        Path file = Files.writeString(dir.resolve("source.txt"), "data");

        assertThrows(NotDirectoryException.class, () -> ConfinedTree.at(file).walk(1_000,
                new ConfinedTree.Entries() {
                    @Override
                    public void reached(ConfinedTree.Reached entry) {}
                }));
    }

    @Test
    void aRootThatIsALinkToNothingIsNotThere(@TempDir Path dir) throws IOException {
        Path root = dir.resolve("root");
        link(root, dir.resolve("absent"));

        assertThrows(NoSuchFileException.class, () -> ConfinedTree.at(root).walk(1_000,
                new ConfinedTree.Entries() {
                    @Override
                    public void reached(ConfinedTree.Reached entry) {}
                }));
    }

    @Test
    void aWalkReportsTheDirectoriesItReachesAndGoesNoDeeperThanItIsAsked(@TempDir Path dir)
            throws IOException {
        Files.createDirectories(dir.resolve("a/b/c"));
        Files.writeString(dir.resolve("a/b/c/deep.sou"), "deep");
        Files.writeString(dir.resolve("a/shallow.sou"), "shallow");
        List<String> directories = new ArrayList<>();
        List<String> files = new ArrayList<>();

        ConfinedTree.at(dir).walk(1_000, 2, entry -> {
            switch (entry) {
                case ConfinedTree.Reached.RegularFile file -> files.add(file.relative());
                case ConfinedTree.Reached.Directory directory -> directories.add(directory.relative());
                case ConfinedTree.Reached.Link _, ConfinedTree.Reached.Other _ -> {
                }
            }
        });

        assertEquals(List.of("", "a", "a/b"), directories.stream().sorted().toList());
        assertEquals(List.of("a/shallow.sou"), files);
    }

    @Test
    void aRootThatIsNotThereIsReportedRatherThanWalkedAsEmpty(@TempDir Path dir) {
        assertThrows(IOException.class, () -> ConfinedTree.at(dir.resolve("absent")).walk(1_000,
                new ConfinedTree.Entries() {
                    @Override
                    public void reached(ConfinedTree.Reached entry) {}
                }));
    }
    @Test
    void aStreamIsReadUpToTheLimitAndNoFurther() throws IOException {
        assertArrayEquals(new byte[]{1, 2, 3}, BoundedRead.bytes(new ByteArrayInputStream(new byte[]{1, 2, 3}), 3));
        assertThrows(LimitExceededException.class,
                () -> BoundedRead.bytes(new ByteArrayInputStream(new byte[]{1, 2, 3}), 2));
    }
}
