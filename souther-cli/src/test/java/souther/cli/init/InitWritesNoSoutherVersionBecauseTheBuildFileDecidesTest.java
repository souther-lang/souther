package souther.cli.init;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a build file is written the build decides which Souther runs, so {@code souther init} writes
 * no {@code .souther-version} beside it. One a user adds constrains direct use of the command line
 * only, which is the file's whole claim.
 */
class InitWritesNoSoutherVersionBecauseTheBuildFileDecidesTest {

    private static final String VERSION_FILE = ".souther-version";

    private static int init(Path directory, String build) {
        ByteArrayOutputStream sink = new ByteArrayOutputStream();
        PrintStream said = new PrintStream(sink, true, StandardCharsets.UTF_8);
        return InitCommand.run(new String[] {"com.example:hello", "--build", build,
                "-d", directory.toString()}, Locale.ENGLISH, said, said, directory, "9.9.9");
    }

    @Test
    void aMavenProjectIsWrittenWithoutOne(@TempDir Path parent) {
        Path project = parent.resolve("maven");

        assertEquals(0, init(project, "maven"));

        assertTrue(Files.exists(project.resolve("pom.xml")));
        assertFalse(Files.exists(project.resolve(VERSION_FILE)));
    }

    @Test
    void aGradleProjectIsWrittenWithoutOne(@TempDir Path parent) {
        Path project = parent.resolve("gradle");

        assertEquals(0, init(project, "gradle"));

        assertTrue(Files.exists(project.resolve("build.gradle.kts")));
        assertFalse(Files.exists(project.resolve(VERSION_FILE)));
    }
}
