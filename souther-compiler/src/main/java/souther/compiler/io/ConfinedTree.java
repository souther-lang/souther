package souther.compiler.io;

import java.io.IOException;
import java.io.InputStream;
import java.nio.ByteBuffer;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.FileVisitOption;
import java.nio.file.FileVisitResult;
import java.nio.file.FileVisitor;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.LinkOption;
import java.nio.file.NoSuchFileException;
import java.nio.file.NotDirectoryException;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.BasicFileAttributes;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

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

    /** What the root resolves to, worked out once and only after the root exists. */
    private Path realRoot;

    /**
     * Directories below the root found not to be links, so that a walk that reads many files under
     * the same directories does not look at each directory again for every file. It is what this
     * instance has seen: an instance is for one operation, and is not kept across the time in which
     * a directory could be replaced.
     */
    private final Set<Path> checked = ConcurrentHashMap.newKeySet();

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

    /**
     * What the file {@code relative} holds, or nothing when there is no such regular file to read —
     * because there is none, because it is not a regular file, or because its name is refused. One
     * resolution of the name, for a caller that would otherwise ask whether the file is there and
     * then read it.
     *
     * @throws LimitExceededException when it holds more than {@code maxBytes}
     */
    public Optional<byte[]> readIfPresent(String relative, long maxBytes) throws IOException {
        Path file;
        try {
            file = resolve(relative);
        } catch (ConfinementException _) {
            return Optional.empty();
        }
        try {
            if (!Files.readAttributes(file, BasicFileAttributes.class, LinkOption.NOFOLLOW_LINKS)
                    .isRegularFile()) {
                return Optional.empty();
            }
            try (InputStream in = Files.newInputStream(file, LinkOption.NOFOLLOW_LINKS)) {
                return Optional.of(BoundedRead.bytes(in, maxBytes));
            }
        } catch (NoSuchFileException _) {
            return Optional.empty();
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
            if (Listing.anyIn(directory)) {
                return;
            }
            Files.delete(directory);
            directory = directory.getParent();
        }
    }

    /**
     * An entry a walk reached and could read, as what it is on disk, named relative to the root with
     * {@code /} between components; the root itself is {@code ""}. A caller is handed one of these
     * and says what each kind means to it, in a switch the compiler holds to every kind: a kind a
     * caller was not asked about is a kind it passes over without knowing, which is how a {@code .sou}
     * that was a directory was left out of a tree of sources.
     */
    public sealed interface Reached {

        String relative();

        /** A regular file. */
        record RegularFile(String relative) implements Reached {}

        /** A directory, reported before what is in it; one the depth stops at is not gone into. */
        record Directory(String relative) implements Reached {}

        /** A link, which the walk did not go through. */
        record Link(String relative) implements Reached {}

        /** What is none of those: a pipe, a socket, a device. */
        record Other(String relative) implements Reached {}
    }

    /**
     * What a walk reports. A link is reported and not followed.
     *
     * <p>A walk that did not see the whole tree says so, and by default says so by throwing: a
     * caller that answers "everything under the root" from a walk that skipped a directory it could
     * not open answers with less than there is and does not know it. A caller for whom part of a tree
     * is still an answer says so by overriding {@link #unreadable} or {@link #limitReached}, where
     * the reader of that caller can see it.
     */
    public interface Entries {

        /**
         * Every entry the walk reaches, before it is looked at further — one it could not read
         * among them. Where a caller is asked to stop, or runs out of what it may spend, this is
         * where it says so.
         */
        default void visited() throws IOException {}

        /** An entry the walk reached and could read. */
        void reached(Reached entry) throws IOException;

        /**
         * An entry the walk could not look at or into, or a directory it stopped reading part way
         * through, so whatever is below it was not all seen. The root itself is {@code ""}. Throws
         * {@code cause} unless overridden; returning goes on with the rest of the tree.
         */
        default void unreadable(String relative, IOException cause) throws IOException {
            throw cause;
        }

        /**
         * The walk reached as many entries as it was allowed and stops there, so the rest of the
         * tree was not seen. Throws {@code cause} unless overridden; returning ends the walk with
         * what was reported.
         */
        default void limitReached(LimitExceededException cause) throws IOException {
            throw cause;
        }
    }

    /** As {@link #walk(long, int, Entries)}, to any depth. */
    public void walk(long mostEntries, Entries entries) throws IOException {
        walk(mostEntries, Integer.MAX_VALUE, entries);
    }

    /**
     * Walks the tree without following a link, reaching at most {@code mostEntries} entries and
     * going at most {@code deepest} directories down. An entry it could not read, a directory it
     * could not read to the end, and reaching the limit are reported to {@code entries}, which
     * throws for each unless it says otherwise.
     *
     * @throws NoSuchFileException when the root is not there, or is a link to nothing
     * @throws NotDirectoryException when the root is not a directory
     */
    public void walk(long mostEntries, int deepest, Entries entries) throws IOException {
        // The root is the caller's own, so a link in the way to it is walked through; the walk
        // starts from what it resolves to, which is the one place a link is followed. What it
        // resolves to is a tree only if it is a directory: a file or nothing at all is not an empty
        // tree, and walked as one it would answer with nothing found.
        Path start = root.toRealPath();
        if (!Files.readAttributes(start, BasicFileAttributes.class).isDirectory()) {
            throw new NotDirectoryException(root.toString());
        }
        Files.walkFileTree(start, EnumSet.noneOf(FileVisitOption.class), deepest,
                new Walker(start, mostEntries, entries));
    }

    /**
     * What a walk does at each of the four places {@link Files#walkFileTree} reaches it, every one
     * written here: inherited, one of them would say nothing of an entry it could not read, or count
     * none of what it reached.
     */
    static final class Walker implements FileVisitor<Path> {

        private final Path start;
        private final long mostEntries;
        private final Entries entries;
        private long reached;

        Walker(Path start, long mostEntries, Entries entries) {
            this.start = start;
            this.mostEntries = mostEntries;
            this.entries = entries;
        }

        @Override
        public FileVisitResult preVisitDirectory(Path dir, BasicFileAttributes attrs)
                throws IOException {
            if (!reach()) {
                return FileVisitResult.TERMINATE;
            }
            entries.reached(new Reached.Directory(spelled(start, dir)));
            return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
            if (!reach()) {
                return FileVisitResult.TERMINATE;
            }
            String relative = spelled(start, file);
            entries.reached(attrs.isSymbolicLink() ? new Reached.Link(relative)
                    : attrs.isRegularFile() ? new Reached.RegularFile(relative)
                    // One the depth stops at: reached, and not gone into.
                    : attrs.isDirectory() ? new Reached.Directory(relative)
                    : new Reached.Other(relative));
            return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult visitFileFailed(Path file, IOException e) throws IOException {
            if (!reach()) {
                return FileVisitResult.TERMINATE;
            }
            entries.unreadable(spelled(start, file),
                    new IOException("could not read " + file + ": " + e, e));
            return FileVisitResult.CONTINUE;
        }

        @Override
        public FileVisitResult postVisitDirectory(Path dir, IOException e) throws IOException {
            // Reached already, on the way in. An error here is one met while reading what the
            // directory holds, so what came after it in the directory was not seen.
            if (e != null) {
                entries.unreadable(spelled(start, dir),
                        new IOException("could not read all of " + dir + ": " + e, e));
            }
            return FileVisitResult.CONTINUE;
        }

        private boolean reach() throws IOException {
            entries.visited();
            if (++reached > mostEntries) {
                entries.limitReached(new LimitExceededException(
                        "more than " + mostEntries + " entries under " + start));
                return false;
            }
            return true;
        }
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
            boolean directory = i < names.size() - 1;
            if (directory && checked.contains(at)) {
                continue;
            }
            if (Files.isSymbolicLink(at)) {
                throw new ConfinementException(relative + " goes through a link");
            }
            if (create && directory && !Files.exists(at, LinkOption.NOFOLLOW_LINKS)) {
                Files.createDirectory(at);
            }
            if (directory && Files.isDirectory(at, LinkOption.NOFOLLOW_LINKS)) {
                checked.add(at);
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
        if (LINKS_ARE_THE_ONLY_REDIRECT) {
            return;
        }
        Path realRoot = realRoot();
        if (realRoot == null) {
            return;
        }
        Path present = at;
        while (present != null && !Files.exists(present, LinkOption.NOFOLLOW_LINKS)) {
            present = present.getParent();
        }
        if (present != null && !present.toRealPath().startsWith(realRoot)) {
            throw new ConfinementException(relative + " resolves outside " + root);
        }
    }

    /** What the root resolves to, once it exists; {@code null} until then. */
    private Path realRoot() throws IOException {
        if (realRoot == null && Files.exists(root)) {
            realRoot = root.toRealPath();
        }
        return realRoot;
    }

    /**
     * Whether a link is the one way a component of a path can lead elsewhere. On a POSIX file system
     * it is, and the walk over components has already refused it; asking the file system where the
     * path really goes would repeat that at the price of resolving every path in full. Windows has
     * junctions, which are not links, so it is asked there.
     */
    private static final boolean LINKS_ARE_THE_ONLY_REDIRECT =
            FileSystems.getDefault().supportedFileAttributeViews().contains("posix");

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
