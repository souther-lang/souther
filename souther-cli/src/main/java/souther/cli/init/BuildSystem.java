package souther.cli.init;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * The build a project is run by, which decides what {@code init} writes and what it edits.
 *
 * <p>Also how a project is recognised as one that already exists. A directory holding a build file
 * is a project somebody else laid out, and what this command does there is add a source directory
 * and one declaration — not lay out a second project inside it.
 */
public enum BuildSystem {

    MAVEN("maven", "pom.xml"),
    GRADLE("gradle", "build.gradle.kts", "build.gradle");

    private final String spelling;

    /** The files that say a directory holds this build, the first being the one it is created as. */
    private final List<String> buildFiles;

    BuildSystem(String spelling, String... buildFiles) {
        this.spelling = spelling;
        this.buildFiles = List.of(buildFiles);
    }

    String spelling() {
        return spelling;
    }

    /** What a build file created from nothing is called. */
    String buildFile() {
        return buildFiles.get(0);
    }

    /** The build this text names, or null where it names none. */
    static BuildSystem written(String text) {
        for (BuildSystem build : values()) {
            if (build.spelling.equals(text)) {
                return build;
            }
        }
        return null;
    }

    /** Every build, in the order a refusal lists them. */
    static List<String> spellings() {
        return java.util.Arrays.stream(values()).map(BuildSystem::spelling).toList();
    }

    /**
     * The build file this directory holds, or null where it holds none of this build's.
     *
     * <p>A Gradle build is either of two files and a project may hold both, so the answer is the
     * one this build is driven by rather than the set of what is there.
     */
    Path fileIn(Path directory) {
        for (String name : buildFiles) {
            Path file = directory.resolve(name);
            if (Files.isRegularFile(file)) {
                return file;
            }
        }
        return null;
    }

    /**
     * Every build the directory holds, in the order this table writes them.
     *
     * <p>All of them, and not the first. A directory holding both a pom and a Gradle script is a
     * directory where which build a model belongs to is a question, and answering it by which of
     * the two this enum happens to write first is deciding it by an iteration order.
     */
    static List<BuildSystem> everyIn(Path directory) {
        List<BuildSystem> found = new ArrayList<>();
        for (BuildSystem build : values()) {
            if (build.fileIn(directory) != null) {
                found.add(build);
            }
        }
        return found;
    }
}
