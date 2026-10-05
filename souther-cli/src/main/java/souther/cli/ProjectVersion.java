package souther.cli;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

/**
 * The Souther a project says its direct command-line use requires, read from the nearest
 * {@code .souther-version} at or above a directory.
 *
 * <p>An assertion and not a selection: the file names the version a command must be run under, and
 * nothing here finds another Souther to run it under. The file holds one line, an exact version,
 * compared as text — no range and no alias, and nothing normalised on the way: a line with
 * whitespace in it, a blank line after it, or no line at all names no version, and what a file that
 * does not is refused for is said rather than read as the nearest thing it resembles.
 */
sealed interface ProjectVersion {

    /** The file's name, which is also what a refusal names. */
    String FILE = ".souther-version";

    /** No file at or above the directory. */
    record Absent() implements ProjectVersion {}

    /** The nearest file, and the version it names. */
    record Declared(Path file, String version) implements ProjectVersion {}

    /** The nearest file, which does not hold exactly one version on one line. */
    record Malformed(Path file) implements ProjectVersion {}

    /** The nearest file, which could not be read, and why. */
    record Unreadable(Path file, String reason) implements ProjectVersion {}

    /**
     * What the nearest file at or above {@code directory} says. The nearest one wins.
     *
     * <p>Whatever is named that is there is the file, a directory included: a project that holds
     * something it did not mean to under this name is told so, and not run as though it held none.
     */
    static ProjectVersion nearest(Path directory) {
        for (Path at = directory.toAbsolutePath().normalize(); at != null; at = at.getParent()) {
            Path file = at.resolve(FILE);
            if (Files.exists(file)) {
                return read(file);
            }
        }
        return new Absent();
    }

    private static ProjectVersion read(Path file) {
        List<String> lines;
        try {
            lines = Files.readAllLines(file);
        } catch (IOException e) {
            return new Unreadable(file, e.getMessage() == null
                    ? e.getClass().getSimpleName() : e.getMessage());
        }
        boolean oneVersion = lines.size() == 1 && !lines.get(0).isEmpty()
                && lines.get(0).chars().noneMatch(Character::isWhitespace);
        return oneVersion ? new Declared(file, lines.get(0)) : new Malformed(file);
    }
}
