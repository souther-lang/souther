package souther.cli.backend;

import java.io.IOException;
import java.io.InputStream;
import java.nio.file.Files;
import java.nio.file.LinkOption;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import java.util.Set;
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
 * searched in the order given and the first that holds the target at all decides: a development
 * build that stands in for a packaged one is the answer even when it is not usable, and a stale one
 * is refused as such rather than being passed over for another.
 */
public final class Backends {

    /** Where a backend jar states what it is. */
    public static final String DESCRIPTOR = "META-INF/souther/backend.properties";

    private static final String NAME = "name";
    private static final String SOUTHER_VERSION = "souther.version";

    /** What a descriptor says, and the jar it was read from. */
    public record Backend(String name, String southerVersion, Path jar) {}

    /** Why a target cannot be run: a catalog key and what fills it. */
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

    /** The directories to search, in the order they are searched. */
    public Backends(List<Path> directories) {
        this.directories = List.copyOf(directories);
    }

    /**
     * The directories this Souther looks in: {@code $SOUTHER_HOME/backends} first, so that a build
     * under development stands in for an installed one, then the one a package manager's launcher
     * names with {@code souther.backends}. No install prefix is worked out from where this runs.
     */
    public static Backends installed() {
        List<Path> directories = new ArrayList<>();
        String home = System.getenv("SOUTHER_HOME");
        if (home != null && !home.isBlank()) {
            directories.add(Path.of(home, "backends"));
        }
        String packaged = System.getProperty("souther.backends");
        if (packaged != null && !packaged.isBlank()) {
            directories.add(Path.of(packaged));
        }
        return new Backends(directories);
    }

    /**
     * The backend for {@code target} that was built against {@code southerVersion}.
     *
     * @throws Refused where the target is not installed, is installed for other versions only, is
     *         installed twice for this one, or is held by something that is not a backend
     */
    public Backend choose(String target, String southerVersion) throws Refused {
        for (Path directory : directories) {
            List<Backend> named = new ArrayList<>();
            for (Backend backend : scan(directory)) {
                if (backend.name().equals(target)) {
                    named.add(backend);
                }
            }
            if (named.isEmpty()) {
                continue;
            }
            List<Backend> built = named.stream()
                    .filter(backend -> backend.southerVersion().equals(southerVersion)).toList();
            if (built.size() == 1) {
                return built.get(0);
            }
            if (built.size() > 1) {
                throw new Refused("cli.backend.duplicate", target, southerVersion,
                        String.join(", ", built.stream().map(b -> b.jar().toString()).toList()));
            }
            Set<String> versions = new TreeSet<>();
            named.forEach(backend -> versions.add(backend.southerVersion()));
            throw new Refused("cli.backend.version", target, String.join(", ", versions),
                    southerVersion);
        }
        Set<String> installed = new TreeSet<>();
        for (Path directory : directories) {
            scan(directory).forEach(backend -> installed.add(backend.name()));
        }
        throw installed.isEmpty()
                ? new Refused("cli.backend.unknown.none", target)
                : new Refused("cli.backend.unknown", target, String.join(", ", installed));
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
        List<Path> entries;
        try (var listing = Files.list(directory)) {
            entries = listing.filter(entry -> entry.getFileName().toString().endsWith(".jar"))
                    .sorted().toList();
        } catch (IOException e) {
            throw new Refused("cli.backend.directory", directory, e.getMessage());
        }
        List<Backend> found = new ArrayList<>();
        for (Path entry : entries) {
            if (!Files.exists(entry)) {
                // Only a link can be here and name nothing; a regular file exists.
                throw new Refused("cli.backend.link", entry);
            }
            if (Files.isRegularFile(entry)) {
                found.add(describe(entry));
            }
        }
        return found;
    }

    /** What the jar's descriptor says, without loading anything from it. */
    private static Backend describe(Path jar) throws Refused {
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
    private static boolean bare(String value) {
        return value != null && !value.isEmpty()
                && value.chars().noneMatch(Character::isWhitespace);
    }
}
