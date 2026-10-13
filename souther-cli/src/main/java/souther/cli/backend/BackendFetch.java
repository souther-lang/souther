package souther.cli.backend;

import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.nio.file.attribute.PosixFileAttributeView;
import java.nio.file.attribute.PosixFilePermission;
import java.nio.file.attribute.PosixFilePermissions;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Fetches a target's backend from a repository into the directory a fetched backend goes to.
 *
 * <p>The jar is written to a file in that directory whose name a search does not read as a
 * backend, held to its descriptor, and only then moved under the pair's name. A fetch that stops
 * part way — the connection drops, the run is ended — leaves nothing a search finds, and the
 * backend that was there before, if one was, stays usable throughout.
 *
 * <p>Two runs fetching into one directory take turns, under a lock on a file there. The one that
 * waited looks again before it asks the repository, so a compile that waited for another compile's
 * fetch runs what that one fetched.
 */
public final class BackendFetch {

    private BackendFetch() {}

    /** Held by a run of this JVM while it fetches, since a file lock is the process's own. */
    private static final Object FETCHING = new Object();

    private static final String LOCK = ".fetching.lock";

    private static final Set<PosixFilePermission> READABLE =
            PosixFilePermissions.fromString("rw-r--r--");

    /** What came of a fetch. */
    public sealed interface Outcome permits Fetched, Present, Current, Failed {}

    /** The release was fetched, and is the backend for the pair. */
    public record Fetched(Backends.Backend backend, Central.Release release) implements Outcome {}

    /** The pair was there when it was looked for again, so nothing was fetched. */
    public record Present(Backends.Backend backend) implements Outcome {}

    /**
     * The newest release is the one fetched before and is still in place, so it was not fetched
     * again.
     */
    public record Current(Backends.Backend backend, Central.Release release) implements Outcome {}

    /** Nothing was fetched, for the reason the repository gave. */
    public record Failed(Central.Failure failure) implements Outcome {}

    /**
     * The backend for the pair, fetched where the directories still do not hold it once this run has
     * the directory to itself.
     */
    public static Outcome whereAbsent(Backends backends, Central central, String target,
                                      String southerVersion, Consumer<Central.Release> starting)
            throws Backends.Refused, IOException, InterruptedException {
        return fetch(backends, central, target, southerVersion, starting, true);
    }

    /**
     * The newest release for the pair, fetched whether or not one is held, in place of one this
     * command fetched before.
     */
    public static Outcome again(Backends backends, Central central, String target,
                                String southerVersion, Consumer<Central.Release> starting)
            throws Backends.Refused, IOException, InterruptedException {
        return fetch(backends, central, target, southerVersion, starting, false);
    }

    private static Outcome fetch(Backends backends, Central central, String target,
                                 String southerVersion, Consumer<Central.Release> starting,
                                 boolean onlyWhereAbsent)
            throws Backends.Refused, IOException, InterruptedException {
        // Before the directory is made or locked: a target with nothing to ask for, or a setting
        // that names nothing to ask, is answered without touching the disk.
        Central.Failure unasked = central.unaskable(target);
        if (unasked != null) {
            return new Failed(unasked);
        }
        Path directory = Files.createDirectories(backends.fetched());
        synchronized (FETCHING) {
            try (FileChannel channel = FileChannel.open(directory.resolve(LOCK),
                    StandardOpenOption.CREATE, StandardOpenOption.WRITE);
                 FileLock _ = channel.lock()) {
                if (onlyWhereAbsent
                        && backends.find(target, southerVersion) instanceof Backends.Found found) {
                    return new Present(found.backend());
                }
                return switch (central.release(target, southerVersion)) {
                    case Central.Failure failure -> new Failed(failure);
                    case Central.Release release -> {
                        Backends.Backend held = heldAs(backends, release, southerVersion);
                        if (held != null) {
                            yield new Current(held, release);
                        }
                        Path name = backends.fetchedAs(release.target(), southerVersion);
                        backends.clearToFetch(release.target(), southerVersion,
                                Files.isRegularFile(record(name)));
                        starting.accept(release);
                        yield install(backends, central, release, southerVersion, directory);
                    }
                };
            }
        }
    }

    /**
     * The backend the release was fetched as before, where it is still what the directories
     * choose for the pair, or null.
     *
     * <p>A released file does not change, so a jar fetched from the release's address is that
     * release for as long as it stands under the name it was fetched as. Which address that was is
     * written beside it, after it is in place; a record that names no release or another one asks
     * for the jar again, which costs a download and nothing else. A name with no record at all was
     * not written by a fetch, and is refused before this is asked.
     */
    private static Backends.Backend heldAs(Backends backends, Central.Release release,
                                           String southerVersion)
            throws Backends.Refused, IOException {
        Path jar = backends.fetchedAs(release.target(), southerVersion);
        Path record = record(jar);
        if (!Files.isRegularFile(record)
                || !Files.readString(record).equals(release.jar().toString())) {
            return null;
        }
        return backends.find(release.target(), southerVersion) instanceof Backends.Found found
                && found.backend().jar().equals(jar) ? found.backend() : null;
    }

    /**
     * Where the address a fetched jar came from is written: beside it, under a name no search
     * reads.
     */
    private static Path record(Path jar) {
        return jar.resolveSibling("." + jar.getFileName() + ".fetched");
    }

    private static Outcome install(Backends backends, Central central, Central.Release release,
                                   String southerVersion, Path directory)
            throws Backends.Refused, IOException, InterruptedException {
        Path part = Files.createTempFile(directory, ".fetching-", ".part");
        try {
            central.download(release, part);
            Backends.Backend described;
            try {
                described = Backends.describe(part);
            } catch (Backends.Refused notOne) {
                return notTheBackend(release, southerVersion);
            }
            if (!described.name().equals(release.target())
                    || !described.southerVersion().equals(southerVersion)) {
                return notTheBackend(release, southerVersion);
            }
            // A temporary file is the writer's alone, and the jar it becomes is read by whoever
            // runs this Souther, which in a shared SOUTHER_HOME is not only the one who fetched it.
            if (Files.getFileStore(part).supportsFileAttributeView(PosixFileAttributeView.class)) {
                Files.setPosixFilePermissions(part, READABLE);
            }
            // The record says two things: that the name is a fetch's, by being there, and which
            // release stands under it, by what it holds. It is emptied before the move and filled
            // after, so a run ended between the two leaves a name that is still a fetch's to
            // replace, and that names no release, so the next fetch downloads it again.
            Path record = record(backends.fetchedAs(described.name(), southerVersion));
            Files.writeString(record, "");
            Backends.Backend installed = backends.install(part, described);
            Files.writeString(record, release.jar().toString());
            return new Fetched(installed, release);
        } catch (Central.Stop stop) {
            return new Failed(stop.failure());
        } finally {
            Files.deleteIfExists(part);
        }
    }

    private static Outcome notTheBackend(Central.Release release, String southerVersion) {
        return new Failed(new Central.Failure.NotTheBackend(release.jar(), release.target(),
                southerVersion));
    }
}
