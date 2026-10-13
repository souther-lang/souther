package souther.cli.backend;

import souther.compiler.io.Listing;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.AtomicMoveNotSupportedException;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import java.util.TreeSet;
import java.util.jar.JarFile;
import java.util.zip.ZipEntry;

/**
 * The backends installed beside this Souther, and which of them a target names.
 *
 * <p>A backend is an executable jar, or a link to one, in a directory this class is given. It says
 * what it is in {@value #DESCRIPTOR}: the target it answers to and the Souther it was built
 * against, and nothing else. The descriptor is read as an archive entry, so choosing a backend loads
 * no class of it. What the backend is released as is its own and plays no part here.
 *
 * <p>A backend is identified by the pair, so jars for different Souther versions of one target may
 * stand side by side and only the one built against this Souther is chosen. The directories are
 * searched in the order given and the first that holds the pair decides, so a development build
 * stands in for a packaged one of the same pair. A jar for the target built against another Souther
 * is not the backend for this one wherever it stands, so it hides nothing further down the list: a
 * backend fetched for an earlier Souther does not stand in front of the one a package manager
 * installed for this one.
 *
 * <p>The first directory is also where a backend fetched from a repository is written, so a fetched
 * one is found by the same search and the same descriptor as one put there by hand. It is written
 * under the pair's name, {@code <target>-<version>.jar}, and a record beside it says two things:
 * that a fetch wrote the name, by being there, and which release stands under it, by the address it
 * holds. Every question about either is answered by this class, so what makes a name a fetch's is
 * decided in one place.
 */
public final class Backends {

    /** Where a backend jar states what it is. */
    public static final String DESCRIPTOR = "META-INF/souther/backend.properties";

    private static final String NAME = "name";
    private static final String SOUTHER_VERSION = "souther.version";

    /** What a descriptor says, and the jar it was read from. */
    public record Backend(String name, String southerVersion, Path jar) {}

    /** What the directories answer for one target and one Souther, where nothing in them is broken. */
    public sealed interface Lookup permits Found, Absent {}

    /** The backend for the pair. */
    public record Found(Backend backend) implements Lookup {}

    /** No directory holds the pair. {@code searched} is what each directory held, in order. */
    public record Absent(String target, String southerVersion, List<Searched> searched)
            implements Lookup {

        public Absent {
            searched = List.copyOf(searched);
        }
    }

    /** What one directory held, as far as one target is concerned. */
    public sealed interface Searched {

        Path directory();

        /** The directory does not exist. */
        record NotThere(Path directory) implements Searched {}

        /**
         * The directory holds backends, none of them for the target. {@code targets} is what they
         * answer to, sorted, and empty where the directory holds no backend.
         */
        record OtherTargets(Path directory, List<String> targets) implements Searched {

            public OtherTargets {
                targets = List.copyOf(new TreeSet<>(targets));
            }
        }

        /** The directory holds the target, built against the other Southers {@code versions}. */
        record OtherVersions(Path directory, List<String> versions) implements Searched {

            public OtherVersions {
                versions = List.copyOf(new TreeSet<>(versions));
            }
        }
    }

    /**
     * Why the directories cannot be searched, or a backend cannot be put in one: a catalog key and
     * what fills it.
     */
    public static final class Refused extends Exception {

        private static final long serialVersionUID = 1L;

        private final String key;
        private final transient Object[] arguments;

        Refused(String key, Object... arguments) {
            super(key);
            this.key = key;
            this.arguments = arguments;
        }

        public String key() {
            return key;
        }

        public Object[] arguments() {
            return arguments.clone();
        }
    }

    private final List<Path> directories;

    /** The directories to search, in the order they are searched; the first is written to. */
    public Backends(List<Path> directories) {
        if (directories.isEmpty()) {
            throw new IllegalArgumentException("a fetched backend has nowhere to go");
        }
        this.directories = List.copyOf(directories);
    }

    /**
     * The directories this Souther looks in: {@code $SOUTHER_HOME/backends} where that is set and
     * {@code .souther/backends} under the user's home where it is not, then the one a package
     * manager's launcher names with {@code souther.backends}. The first comes before the packaged
     * one so that a build under development, or a backend fetched for this Souther, stands in for
     * what was installed with it. No install prefix is worked out from where this runs.
     */
    public static Backends installed() {
        List<Path> directories = new ArrayList<>();
        String home = System.getenv("SOUTHER_HOME");
        directories.add(home != null && !home.isBlank() ? Path.of(home, "backends")
                : Path.of(System.getProperty("user.home"), ".souther", "backends"));
        String packaged = System.getProperty("souther.backends");
        if (packaged != null && !packaged.isBlank()) {
            directories.add(Path.of(packaged));
        }
        return new Backends(directories);
    }

    /** Where a fetched backend is written. */
    public Path fetched() {
        return directories.getFirst();
    }

    /**
     * The name a fetched backend for the release's target and {@code southerVersion} is written
     * under. Built from a release, which exists only for a target the repository's table has, and
     * from this Souther's version, so no name a command line or a jar gave is ever made a path.
     */
    Path fetchedAs(Central.Release release, String southerVersion) {
        return fetched().resolve(release.target() + "-" + southerVersion + ".jar");
    }

    /**
     * The backend for {@code target} that was built against {@code southerVersion}, or what each
     * directory held instead.
     *
     * @throws Refused where the target is installed twice for this Souther, or a directory holds
     *         something that is not a backend, or cannot be listed
     */
    public Lookup find(String target, String southerVersion) throws Refused {
        List<Searched> searched = new ArrayList<>();
        for (Path directory : directories) {
            if (!Files.exists(directory, LinkOption.NOFOLLOW_LINKS)) {
                searched.add(new Searched.NotThere(directory));
                continue;
            }
            List<Backend> held = scan(directory);
            List<Backend> named = held.stream()
                    .filter(backend -> backend.name().equals(target)).toList();
            if (named.isEmpty()) {
                searched.add(new Searched.OtherTargets(directory,
                        held.stream().map(Backend::name).toList()));
                continue;
            }
            List<Backend> built = named.stream()
                    .filter(backend -> backend.southerVersion().equals(southerVersion)).toList();
            if (built.size() == 1) {
                return new Found(built.getFirst());
            }
            if (built.size() > 1) {
                throw duplicate(target, southerVersion, built);
            }
            searched.add(new Searched.OtherVersions(directory,
                    named.stream().map(Backend::southerVersion).toList()));
        }
        return new Absent(target, southerVersion, searched);
    }

    /** The record beside a fetched jar, under a name no search reads as a backend. */
    private static Path record(Path jar) {
        return jar.resolveSibling("." + jar.getFileName() + ".fetched");
    }

    /**
     * The backend the release was fetched as before, where it is still what the directories choose
     * for the pair, or null.
     *
     * <p>A released file does not change, so a jar fetched from the release's address is that
     * release for as long as it stands under the name it was fetched as. A record that names no
     * release, or another one, means the jar is to be fetched again, which costs a download and
     * nothing else.
     */
    Backend fetchedBefore(Central.Release release, String southerVersion)
            throws Refused, IOException {
        Path jar = fetchedAs(release, southerVersion);
        Path record = record(jar);
        if (!Files.isRegularFile(record)
                || !Files.readString(record).equals(release.jar().toString())) {
            return null;
        }
        return find(release.target(), southerVersion) instanceof Found found
                && found.backend().jar().equals(jar) ? found.backend() : null;
    }

    /**
     * Refuses a fetch for the pair that would replace or stand beside a jar someone else put in the
     * directory a fetched backend goes to.
     *
     * <p>A fetch replaces what is under the pair's name only where a fetch wrote it, which the
     * record says. A jar under that name with no record was put there by hand, whatever it
     * describes, and so is a jar for the pair under any other name. Asked before anything is
     * downloaded, since the answer is the directory's and not the release's. Something under the
     * name that is not a backend at all is refused as such, as every search refuses it.
     *
     * @throws Refused where the directory holds such a jar, or cannot be listed
     */
    void clearToFetch(Central.Release release, String southerVersion) throws Refused {
        Path name = fetchedAs(release, southerVersion);
        boolean fetchedThere = Files.isRegularFile(record(name));
        for (Backend backend : scan(fetched())) {
            boolean ours = backend.jar().equals(name) && fetchedThere;
            boolean pair = backend.name().equals(release.target())
                    && backend.southerVersion().equals(southerVersion);
            if (!ours && (pair || backend.jar().equals(name))) {
                throw new Refused("cli.backend.fetch.held", release.target(), southerVersion,
                        backend.jar());
            }
        }
    }

    /**
     * Puts the jar at {@code downloaded}, which was held to its descriptor as the release's, in the
     * directory a fetched backend goes to under the pair's name, replacing what a fetch wrote there
     * before, and answers with it as it is found there. {@link #clearToFetch} is asked first.
     *
     * <p>The move is atomic, so a search running at the same time sees the old jar or the new one
     * and nothing between them; {@code downloaded} has to be in the same directory, and named so
     * that a search does not read it as a backend. The record is emptied before the move and
     * filled after, so a run ended between the two leaves a name that is still a fetch's to
     * replace, and that names no release, so the next fetch downloads it again.
     *
     * @throws IOException where the move fails, the jar is left where it was
     */
    Backend install(Path downloaded, Central.Release release, String southerVersion)
            throws IOException {
        Path directory = fetched();
        Path target = fetchedAs(release, southerVersion);
        Path record = record(target);
        Files.writeString(record, "");
        try {
            Files.move(downloaded, target, StandardCopyOption.ATOMIC_MOVE,
                    StandardCopyOption.REPLACE_EXISTING);
        } catch (AtomicMoveNotSupportedException e) {
            throw new IOException(directory + " cannot replace a file atomically", e);
        }
        Files.writeString(record, release.jar().toString());
        return new Backend(release.target(), southerVersion, target);
    }

    private static Refused duplicate(String target, String southerVersion, List<Backend> built) {
        return new Refused("cli.backend.duplicate", target, southerVersion,
                String.join(", ", built.stream().map(b -> b.jar().toString()).toList()));
    }

    /** The backends in one directory, which holds none where it does not exist. */
    private static List<Backend> scan(Path directory) throws Refused {
        if (!Files.isDirectory(directory)) {
            // Absent is no backends. What is there under the name and is not a directory — a file,
            // or a link to nothing — is an install that is not what it was meant to be, and is said.
            if (Files.exists(directory, LinkOption.NOFOLLOW_LINKS)) {
                throw new Refused("cli.backend.directory", directory, "not a directory");
            }
            return List.of();
        }
        List<Path> entries = new ArrayList<>();
        try {
            Listing.each(directory, entry -> {
                if (entry.getFileName().toString().endsWith(".jar")) {
                    entries.add(entry);
                }
            });
            entries.sort(null);
        } catch (IOException e) {
            throw new Refused("cli.backend.directory", directory, e.getMessage());
        }
        List<Backend> found = new ArrayList<>();
        for (Path entry : entries) {
            if (!Files.exists(entry)) {
                // Only a link can be here and name nothing; a regular file exists.
                throw new Refused("cli.backend.link", entry);
            }
            if (!Files.isRegularFile(entry)) {
                // Named as a backend and not a file: a directory or a pipe is a backend that is
                // not what it was meant to be, as a file that is not a jar is, and is said.
                throw new Refused("cli.backend.descriptor", entry);
            }
            found.add(describe(entry));
        }
        return found;
    }

    /** What the jar's descriptor says, without loading anything from it. */
    static Backend describe(Path jar) throws Refused {
        Properties descriptor = new Properties();
        try (JarFile archive = new JarFile(jar.toFile())) {
            ZipEntry entry = archive.getEntry(DESCRIPTOR);
            if (entry == null) {
                throw new Refused("cli.backend.descriptor", jar);
            }
            try (InputStream in = archive.getInputStream(entry)) {
                descriptor.load(in);
            }
        } catch (IOException | IllegalArgumentException e) {
            throw new Refused("cli.backend.descriptor", jar);
        }
        String name = descriptor.getProperty(NAME);
        String version = descriptor.getProperty(SOUTHER_VERSION);
        if (descriptor.size() != 2 || !bare(name) || !bare(version)) {
            throw new Refused("cli.backend.descriptor", jar);
        }
        return new Backend(name, version, jar);
    }

    /**
     * Whether the value is a word: present, not empty, and with no whitespace in it.
     *
     * <p>What the descriptor says is compared as written, as {@code .souther-version} is, so a value
     * that only matches once it has been trimmed is refused and not trimmed.
     */
    static boolean bare(String value) {
        return value != null && !value.isEmpty()
                && value.chars().noneMatch(Character::isWhitespace);
    }
}
