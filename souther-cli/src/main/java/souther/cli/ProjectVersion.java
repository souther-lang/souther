package souther.cli;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;

/**
 * The Souther a project says its direct command-line use requires, read from the nearest
 * {@code .souther-version} at or above a directory.
 *
 * <p>An assertion and not a selection: the file names the version a command must be run under, and
 * nothing here finds another Souther to run it under. The file holds one line, an exact version,
 * compared as text — no range and no alias, so what it asserts is the same to every reader.
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

    /** What the nearest file at or above {@code directory} says. The nearest one wins. */
    static ProjectVersion nearest(Path directory) {
        for (Path at = directory.toAbsolutePath().normalize(); at != null; at = at.getParent()) {
            Path file = at.resolve(FILE);
            if (Files.isRegularFile(file)) {
                return read(file);
            }
        }
        return new Absent();
    }

    private static ProjectVersion read(Path file) {
        String line;
        try {
            line = Files.readString(file).strip();
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        boolean oneWord = !line.isEmpty() && line.chars().noneMatch(Character::isWhitespace);
        return oneWord ? new Declared(file, line) : new Malformed(file);
    }
}
