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
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

/**
 * Fetches a target's backend from a repository into the directory a fetched backend goes to.
 *
 * <p>A fetch goes through its steps in the order each costs more than the one before, and stops at
 * the first that answers: what can be decided without asking anything — the target has no artifact,
 * a setting names nothing — is decided before the directory is touched; what the directory says —
 * the pair is there by now, the release is the one fetched before, a jar put there by hand would be
 * replaced — is decided before anything is downloaded; and the jar is held to its descriptor before
 * it is put where a search reads it.
 *
 * <p>The jar is written to a file in that directory whose name a search does not read as a
 * backend, and only then moved under the pair's name. A fetch that stops part way — the connection
 * drops, the run is ended — leaves nothing a search finds, and the backend that was there before,
 * if one was, stays usable throughout.
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

    /**
     * Where a fetch asks: a repository the settings name and that can be asked, or settings that
     * name none, which answer every fetch with why.
     */
    public sealed interface Source permits Central, Configured.Unusable {

        /** What a reader is told the repository is called. */
        String name();
    }

    /** What came of a compile's fetch: the pair is there by now, or was fetched, or neither. */
    public sealed interface Supplied permits Asked, Present {}

    /**
     * What came of a fetch the command asked for: the release was fetched, or is the one fetched
     * before, or neither.
     */
    public sealed interface Refreshed permits Asked, Current {}

    /**
     * What came of asking the repository and fetching what it named, which either fetch can end
     * in.
     */
    public sealed interface Asked extends Supplied, Refreshed permits Fetched, Failed {}

    /** The release was fetched, and is the backend for the pair. */
    public record Fetched(Backends.Backend backend, Central.Release release) implements Asked {}

    /** Nothing was fetched, for the reason the repository gave. */
    public record Failed(Central.Failure failure) implements Asked {}

    /** The pair was there when it was looked for again, so nothing was fetched. */
    public record Present(Backends.Backend backend) implements Supplied {}

    /**
     * The newest release is the one fetched before and is still in place, so it was not fetched
     * again.
     */
    public record Current(Backends.Backend backend, Central.Release release) implements Refreshed {}

    /**
     * The backend for the pair, fetched where the directories still do not hold it once this run has
     * the directory to itself.
     */
    public static Supplied whereAbsent(Backends backends, Source source, String target,
                                       String southerVersion, Consumer<Central.Release> starting)
            throws Backends.Refused, IOException, InterruptedException {
        return switch (source) {
            case Configured.Unusable unusable -> new Failed(unusable.why());
            case Central central -> whereAbsent(backends, central, target, southerVersion,
                    starting);
        };
    }

    private static Supplied whereAbsent(Backends backends, Central central, String target,
                                        String southerVersion, Consumer<Central.Release> starting)
            throws Backends.Refused, IOException, InterruptedException {
        Optional<Central.Failure.Unregistered> unregistered = central.unregistered(target);
        if (unregistered.isPresent()) {
            return new Failed(unregistered.get());
        }
        Path directory = Files.createDirectories(backends.fetched());
        synchronized (FETCHING) {
            try (FileChannel channel = lockFile(directory); FileLock _ = channel.lock()) {
                if (backends.find(target, southerVersion) instanceof Backends.Found found) {
                    return new Present(found.backend());
                }
                return switch (central.release(target, southerVersion)) {
                    case Central.Failure failure -> new Failed(failure);
                    case Central.Release release ->
                            download(backends, central, release, southerVersion, directory,
                                    starting);
                };
            }
        }
    }

    /**
     * The newest release for the pair, fetched whether or not one is held, in place of one this
     * command fetched before.
     */
    public static Refreshed again(Backends backends, Source source, String target,
                                  String southerVersion, Consumer<Central.Release> starting)
            throws Backends.Refused, IOException, InterruptedException {
        return switch (source) {
            case Configured.Unusable unusable -> new Failed(unusable.why());
            case Central central -> again(backends, central, target, southerVersion, starting);
        };
    }

    private static Refreshed again(Backends backends, Central central, String target,
                                   String southerVersion, Consumer<Central.Release> starting)
            throws Backends.Refused, IOException, InterruptedException {
        Optional<Central.Failure.Unregistered> unregistered = central.unregistered(target);
        if (unregistered.isPresent()) {
            return new Failed(unregistered.get());
        }
        Path directory = Files.createDirectories(backends.fetched());
        synchronized (FETCHING) {
            try (FileChannel channel = lockFile(directory); FileLock _ = channel.lock()) {
                return switch (central.release(target, southerVersion)) {
                    case Central.Failure failure -> new Failed(failure);
                    case Central.Release release -> {
                        Optional<Backends.Backend> before =
                                backends.fetchedBefore(release, southerVersion);
                        yield before.isPresent() ? new Current(before.get(), release)
                                : download(backends, central, release, southerVersion, directory,
                                        starting);
                    }
                };
            }
        }
    }

    private static FileChannel lockFile(Path directory) throws IOException {
        return FileChannel.open(directory.resolve(LOCK), StandardOpenOption.CREATE,
                StandardOpenOption.WRITE);
    }

    /** Downloads the release, once the directory has said a fetch may write the pair's name. */
    private static Asked download(Backends backends, Central central, Central.Release release,
                                  String southerVersion, Path directory,
                                  Consumer<Central.Release> starting)
            throws Backends.Refused, IOException, InterruptedException {
        backends.clearToFetch(release, southerVersion);
        starting.accept(release);
        Path part = Files.createTempFile(directory, ".fetching-", ".part");
        try {
            central.download(release, part);
            if (!isTheRelease(part, release, southerVersion)) {
                return new Failed(new Central.Failure.NotTheBackend(release.jar(),
                        release.target(), southerVersion));
            }
            // A temporary file is the writer's alone, and the jar it becomes is read by whoever
            // runs this Souther, which in a shared SOUTHER_HOME is not only the one who fetched it.
            if (Files.getFileStore(part).supportsFileAttributeView(PosixFileAttributeView.class)) {
                Files.setPosixFilePermissions(part, READABLE);
            }
            return new Fetched(backends.install(part, release, southerVersion), release);
        } catch (Central.Stop stop) {
            return new Failed(stop.failure());
        } finally {
            Files.deleteIfExists(part);
        }
    }

    /** Whether the downloaded jar's descriptor says it is the release's target, for this Souther. */
    private static boolean isTheRelease(Path part, Central.Release release,
                                        String southerVersion) {
        try {
            Backends.Backend described = Backends.describe(part);
            return described.name().equals(release.target())
                    && described.southerVersion().equals(southerVersion);
        } catch (Backends.Refused _) {
            return false;
        }
    }
}
