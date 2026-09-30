package souther.compiler.io;

import java.io.IOException;
import java.io.InputStream;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileVisitOption;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;

/**
 * A directory, and the files below it that a name found there may reach.
 *
 * <p>A name that came from somewhere other than the caller — a line of a record on disk, a class
 * name from a source file, an entry a walk found — is not a path. Joined onto a directory and handed
 * to {@code Files}, it can leave the directory by a {@code ..}, by being absolute, or by passing
 * through a link that points elsewhere, and only the last of these is invisible to a check made on
 * the text of the path. So the directory is asked, rather than each caller checking the text: every
 * operation here takes a name relative to the root and looks at what is on disk for each component
 * of it, and one that would go through a link is refused whole.
 *
 * <p>The root is the caller's own and is taken as it is; a link in the path to it is the caller's
 * business. Everything below it is what this refuses to follow. A file is opened without following a
 * link as well, so a link put in place after the components were looked at is not followed at the
 * last step either.
 */
public final class ConfinedTree {

    private final Path root;

    private ConfinedTree(Path root) {
        this.root = root;
    }

    /** The tree at {@code root}. Nothing is read from disk until an operation asks. */
    public static ConfinedTree at(Path root) {
        return new ConfinedTree(root.toAbsolutePath().normalize());
    }

    public Path root() {
        return root;
    }

    /**
     * The path {@code relative} names under the root.
     *
     * @throws ConfinementException when the name is not a plain relative path, or when a component of
     *         it that exists is a link or resolves outside the root
     */
    public Path resolve(String relative) throws IOException {
        return locate(relative, false);
    }

    /** Whether {@code relative} names a regular file that may be read. A name refused reads as not one. */
    public boolean isRegularFile(String relative) {
        try {
            Path file = resolve(relative);
            return Files.readAttributes(file, BasicFileAttributes.class, LinkOption.NOFOLLOW_LINKS)
                    .isRegularFile();
        } catch (IOException _) {
            return false;
        }
    }

    /** Whether {@code relative} names a directory below the root. A name refused reads as not one. */
    public boolean isDirectory(String relative) {
        try {
            Path directory = resolve(relative);
            return Files.readAttributes(directory, BasicFileAttributes.class, LinkOption.NOFOLLOW_LINKS)
                    .isDirectory();
        } catch (IOException _) {
            return false;
        }
    }

    /**
     * What the file {@code relative} holds.
     *
     * @throws LimitExceededException when it holds more than {@code maxBytes}
     * @throws ConfinementException when it is not a regular file, or its name is refused
     */
    public byte[] read(String relative, long maxBytes) throws IOException {
        Path file = resolve(relative);
        if (!Files.readAttributes(file, BasicFileAttributes.class, LinkOption.NOFOLLOW_LINKS)
                .isRegularFile()) {
            throw new ConfinementException(relative + " is not a regular file");
        }
        try (InputStream in = Files.newInputStream(file, LinkOption.NOFOLLOW_LINKS)) {
            return BoundedRead.bytes(in, maxBytes);
        }
    }

    /** As {@link #read}, as UTF-8; bytes that are not are an error rather than replaced. */
    public String readString(String relative, long maxBytes) throws IOException {
        return StandardCharsets.UTF_8.newDecoder().decode(ByteBuffer.wrap(read(relative, maxBytes)))
                .toString();
    }

    /**
     * Writes {@code bytes} to {@code relative}, making the directories on the way, and answers the
     * path written. A directory on the way that is a link is an error and is not written through.
     */
    public Path write(String relative, byte[] bytes) throws IOException {
        Files.createDirectories(root);
        Path file = locate(relative, true);
        Files.write(file, bytes, StandardOpenOption.CREATE, StandardOpenOption.TRUNCATE_EXISTING,
                StandardOpenOption.WRITE, LinkOption.NOFOLLOW_LINKS);
        return file;
    }

    /** Deletes the file {@code relative} names, if there is one, and says whether there was. */
    public boolean deleteIfExists(String relative) throws IOException {
        return Files.deleteIfExists(resolve(relative));
    }

    /**
     * Removes the directories above {@code relative}, nearest first, for as long as each is empty,
     * and never the root.
     */
    public void deleteEmptyParents(String relative) throws IOException {
        Path directory = resolve(relative).getParent();
        while (directory != null && !directory.equals(root) && directory.startsWith(root)
                && Files.isDirectory(directory, LinkOption.NOFOLLOW_LINKS)) {
            try (var held = Files.list(directory)) {
                if (held.findAny().isPresent()) {
                    return;
                }
            }
            Files.delete(directory);
            directory = directory.getParent();
        }
    }

    /** What a walk reports. A link is reported and not followed. */
    public interface Entries {

        /** Every entry the walk visits, before it is looked at further. */
        default void visited() {}

        /** A regular file, named relative to the root with {@code /} between components. */
        void regularFile(String relative);

        /** A link, which the walk did not go through. */
        default void link(String relative) {}
    }

    /**
     * Walks the whole tree without following a link, visiting at most {@code mostEntries} entries.
     * An entry that cannot be read is skipped.
     *
     * @return whether the walk reached the end of the tree rather than the limit
     */
    public boolean walk(long mostEntries, Entries entries) throws IOException {
        boolean[] complete = {true};
        long[] visited = {0};
        // The root is the caller's own, so a link in the way to it is walked through; the walk
        // starts from what it resolves to, which is the one place a link is followed.
        Path start = Files.exists(root) ? root.toRealPath() : root;
        Files.walkFileTree(start, EnumSet.noneOf(FileVisitOption.class), Integer.MAX_VALUE,
                new SimpleFileVisitor<>() {
                    @Override
                    public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs) {
                        return count() ? FileVisitResult.CONTINUE : FileVisitResult.TERMINATE;
                    }

                    @Override
                    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) {
                        if (!count()) {
                            return FileVisitResult.TERMINATE;
                        }
                        String relative = spelled(start, file);
                        if (attrs.isSymbolicLink()) {
                            entries.link(relative);
                        } else if (attrs.isRegularFile()) {
                            entries.regularFile(relative);
                        }
                        return FileVisitResult.CONTINUE;
                    }

                    @Override
                    public FileVisitResult visitFileFailed(Path file, IOException e) {
                        return FileVisitResult.CONTINUE;
                    }

                    private boolean count() {
                        entries.visited();
                        if (++visited[0] > mostEntries) {
                            complete[0] = false;
                            return false;
                        }
                        return true;
                    }
                });
        return complete[0];
    }

    private static String spelled(Path start, Path file) {
        List<String> names = new ArrayList<>();
        for (Path name : start.relativize(file)) {
            names.add(name.toString());
        }
        return String.join("/", names);
    }

    private Path locate(String relative, boolean create) throws IOException {
        List<String> names = names(relative);
        Path at = root;
        for (int i = 0; i < names.size(); i++) {
            at = at.resolve(names.get(i));
            if (Files.isSymbolicLink(at)) {
                throw new ConfinementException(relative + " goes through a link");
            }
            if (create && i < names.size() - 1 && !Files.exists(at, LinkOption.NOFOLLOW_LINKS)) {
                Files.createDirectory(at);
            }
        }
        requireInsideRoot(at, relative);
        return at;
    }

    /**
     * What is on disk at the deepest part of {@code at} that exists resolves to somewhere under the
     * root. A link is caught by the walk over components above; this is for what is neither a link
     * nor a plain directory on a platform, such as a junction.
     */
    private void requireInsideRoot(Path at, String relative) throws IOException {
        if (!Files.exists(root)) {
            return;
        }
        Path present = at;
        while (present != null && !Files.exists(present, LinkOption.NOFOLLOW_LINKS)) {
            present = present.getParent();
        }
        if (present != null && !present.toRealPath().startsWith(root.toRealPath())) {
            throw new ConfinementException(relative + " resolves outside " + root);
        }
    }

    private static List<String> names(String relative) throws ConfinementException {
        if (relative.isEmpty() || relative.indexOf('\0') >= 0) {
            throw new ConfinementException("not a relative path: `" + relative + "`");
        }
        Path path;
        try {
            path = Path.of(relative);
        } catch (InvalidPathException _) {
            throw new ConfinementException("not a path: `" + relative + "`");
        }
        if (path.isAbsolute() || path.getRoot() != null) {
            throw new ConfinementException("`" + relative + "` is not relative to the tree");
        }
        List<String> names = new ArrayList<>();
        for (Path name : path) {
            String text = name.toString();
            if (text.isEmpty() || text.equals(".") || text.equals("..")) {
                throw new ConfinementException("`" + relative + "` is not a plain relative path");
            }
            names.add(text);
        }
        return names;
    }
}
