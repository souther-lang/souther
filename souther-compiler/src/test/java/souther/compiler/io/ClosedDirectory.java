package souther.compiler.io;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.PosixFilePermission;
import java.util.Set;

import static org.junit.jupiter.api.Assumptions.assumeTrue;

/**
 * A directory with every permission taken away, put back when the test is done so that the
 * temporary directory can be removed. Where taking them away does not stop this process reading it
 * — a superuser, a file system without POSIX permissions — the test is skipped, since what it is
 * about cannot be made to happen.
 */
public record ClosedDirectory(Path directory, Set<PosixFilePermission> had) implements AutoCloseable {

    public static ClosedDirectory shut(Path directory) throws IOException {
        Set<PosixFilePermission> had;
        try {
            had = Files.getPosixFilePermissions(directory);
        } catch (UnsupportedOperationException e) {
            assumeTrue(false, "permissions cannot be taken away here: " + e);
            throw e;
        }
        Files.setPosixFilePermissions(directory, Set.of());
        ClosedDirectory closed = new ClosedDirectory(directory, had);
        if (Files.isReadable(directory)) {
            closed.close();
            assumeTrue(false, "this process reads a directory with no permissions");
        }
        return closed;
    }

    @Override
    public void close() throws IOException {
        Files.setPosixFilePermissions(directory, had);
    }
}
