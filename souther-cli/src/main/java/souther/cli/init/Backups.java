package souther.cli.init;

import java.io.IOException;
import java.nio.file.Path;
import java.util.concurrent.TimeUnit;

/**
 * Whether the previous contents of a file this command edits have to be left beside it.
 *
 * <p>Left, unless the file is one a version control system is already holding the previous contents
 * of. A {@code .orig} next to a tracked, unmodified file is a second copy of what {@code git diff}
 * would say better, and it is the author who then has to delete it.
 *
 * <p>Both halves are asked. A file git does not track has no previous contents anywhere; a file
 * that is tracked but already edited has a recorded version that is not what this command is about
 * to overwrite.
 */
final class Backups {

    private Backups() {}

    /** Whether a copy has to be left beside {@code file} before it is written over. */
    static boolean areNeededFor(Path file) {
        Path directory = file.toAbsolutePath().getParent();
        String name = file.toAbsolutePath().toString();
        if (!ran(directory, "git", "ls-files", "--error-unmatch", "--", name)) {
            return true;   // untracked, ignored, or not in a repository at all
        }
        return !ran(directory, "git", "diff", "--quiet", "HEAD", "--", name);
    }

    /**
     * Whether the command ran and answered that it succeeded.
     *
     * <p>Anything else — git is not installed, the process was interrupted, it took too long — is
     * answered as though the question could not be settled, and the copy is kept. What this decides
     * is whether the author's own text is recoverable, and the safe answer to not knowing is to
     * leave it beside them.
     */
    private static boolean ran(Path directory, String... command) {
        try {
            Process process = new ProcessBuilder(command)
                    .directory(directory.toFile())
                    .redirectOutput(ProcessBuilder.Redirect.DISCARD)
                    .redirectError(ProcessBuilder.Redirect.DISCARD)
                    .start();
            if (!process.waitFor(10, TimeUnit.SECONDS)) {
                process.destroy();
                return false;
            }
            return process.exitValue() == 0;
        } catch (IOException e) {
            return false;
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            return false;
        }
    }
}
