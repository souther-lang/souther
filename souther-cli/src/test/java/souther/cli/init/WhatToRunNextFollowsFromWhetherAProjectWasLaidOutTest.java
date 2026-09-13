package souther.cli.init;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The command a reader is sent to is one the project they now have can answer.
 *
 * <p>This command has two readings and they leave different projects behind. What it lays out has a
 * model and the rows that pin it down, and the rows are checked by the compile — a test phase there
 * has nothing in it. What it adds to has whatever tests its author wrote, and running those is what
 * says the model now beside them compiles and breaks nothing.
 */
class WhatToRunNextFollowsFromWhetherAProjectWasLaidOutTest {

    @Test
    void aProjectThisCommandLaidOutIsSentToTheCompile(@TempDir Path directory) {
        Run run = run(directory, "com.example:hello");

        assertEquals(0, run.code(), run.err());
        assertTrue(run.out().contains("cd hello && mvn compile"),
                "a project with no test of its own is not sent to its compile:\n" + run.out());
        assertFalse(run.out().contains("mvn test"),
                "a project with no test of its own is sent to a test run:\n" + run.out());
    }

    /**
     * A build that was already there is sent to its own tests.
     *
     * <p>The reading this command takes in somebody's project. A model was added beside their tests,
     * and what says so is a run of them.
     */
    @Test
    void aBuildThatWasAddedToIsSentToItsOwnTests(@TempDir Path directory) throws IOException {
        Files.writeString(directory.resolve("pom.xml"), """
                <project>
                  <groupId>com.acme</groupId>
                  <artifactId>billing</artifactId>
                </project>
                """);

        Run run = run(directory);

        assertEquals(0, run.code(), run.err());
        assertTrue(run.out().contains("mvn test"),
                "a project whose own tests are there is sent past them:\n" + run.out());
    }

    /** The same two answers on Gradle, where the task and not the phase is what is named. */
    @Test
    void gradleIsSentToTheTaskThatMatchesTheReading(@TempDir Path directory) throws IOException {
        Run laidOut = run(directory, "com.example:hello", "--build", "gradle");

        assertEquals(0, laidOut.code(), laidOut.err());
        assertTrue(laidOut.out().contains("./gradlew classes"),
                "a Gradle project with no test of its own is not sent to its classes:\n"
                        + laidOut.out());

        Path theirs = Files.createDirectories(directory.resolve("theirs"));
        Files.writeString(theirs.resolve("build.gradle.kts"), """
                plugins {
                    java
                }

                group = "com.acme"
                """);

        Run addedTo = run(theirs);

        assertEquals(0, addedTo.code(), addedTo.err());
        assertTrue(addedTo.out().contains("./gradlew test"),
                "a Gradle build whose own tests are there is sent past them:\n" + addedTo.out());
    }

    /** What a run wrote to each stream, and what it answered with. */
    private record Run(int code, String out, String err) {}

    private static Run run(Path here, String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = InitCommand.run(args, Locale.ENGLISH,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8), here, "9.9.9");
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
