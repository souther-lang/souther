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
    public sealed interface Outcome permits Fetched, Present, Failed {}

    /** The release was fetched, and is the backend for the pair. */
    public record Fetched(Backends.Backend backend, Central.Release release) implements Outcome {}

    /** The pair was there when it was looked for again, so nothing was fetched. */
    public record Present(Backends.Backend backend) implements Outcome {}

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
                        starting.accept(release);
                        yield install(backends, central, release, southerVersion, directory);
                    }
                };
            }
        }
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
            return new Fetched(backends.install(part, described), release);
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
