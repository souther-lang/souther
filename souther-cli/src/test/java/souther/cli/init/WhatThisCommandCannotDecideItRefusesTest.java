package souther.cli.init;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where this command has no answer, it says so and writes nothing.
 *
 * <p>Every refusal here is a decision somebody else's to make. A group and an artifact are chosen by
 * a person; the coordinate of a project that has a build is written in that build; a module name
 * that does not follow from a coordinate is one the author has to write. Answering any of them with
 * a plausible default is how a project ends up with a name nobody meant and a directory nobody can
 * rename.
 */
class WhatThisCommandCannotDecideItRefusesTest {

    @Test
    void aProjectIsNotStartedWithoutACoordinate(@TempDir Path directory) throws IOException {
        Run run = run(directory);

        assertEquals(2, run.code());
        assertTrue(run.err().contains("<groupId>:<artifactId>"), run.err());
        assertEquals(List.of(), Files.list(directory).toList(), "a refusal wrote something");
    }

    @Test
    void halfACoordinateIsNotACoordinate(@TempDir Path directory) {
        for (String written : List.of("hello", ":hello", "com.example:", "a:b:c")) {
            Run run = run(directory, written);

            assertEquals(2, run.code(), written + " was read as a coordinate");
            assertTrue(run.err().contains(written), run.err());
        }
    }

    /**
     * A build that is there has already answered two of the questions.
     *
     * <p>Refused rather than taken as agreement, even where the line writes what the build says: a
     * line that names a coordinate is a line whose author believes they are choosing one, and a
     * command that quietly used the build's would leave them thinking the project is called
     * something it is not.
     */
    @Test
    void aBuildThatIsThereIsWhatDecidesTheCoordinateAndTheBuild(@TempDir Path directory)
            throws IOException {
        Files.writeString(directory.resolve("pom.xml"), POM);

        assertEquals(2, run(directory, "com.acme:billing").code());
        assertEquals(2, run(directory, "--build", "gradle").code());
        assertTrue(run(directory, "--build", "gradle").err().contains("maven"),
                "the refusal does not say which build is already there");
    }

    /** A pom that names no project is not one a coordinate can be read out of. */
    @Test
    void aBuildThatDoesNotSayWhatItIsCalledIsNotGuessedAt(@TempDir Path directory)
            throws IOException {
        Files.writeString(directory.resolve("pom.xml"), """
                <project>
                  <parent><artifactId>somebody-else</artifactId></parent>
                </project>
                """);

        Run run = run(directory);

        assertEquals(2, run.code());
        assertTrue(run.err().contains("pom.xml"), run.err());
        assertTrue(Files.notExists(directory.resolve("src")), "a refusal wrote a source directory");
    }

    /**
     * A coordinate no module name follows from is answered with the option that writes one.
     *
     * <p>{@code com.data} is an ordinary group and {@code data} is a word the language has taken, so
     * the header derived from it would not parse. What the author is given is the way to say what
     * they want instead.
     */
    @Test
    void aCoordinateThatDerivesNoModuleNameAsksForOne(@TempDir Path directory) {
        Run refused = run(directory, "com.data:hello");

        assertEquals(2, refused.code());
        assertTrue(refused.err().contains("--module"), refused.err());

        Run written = run(directory, "com.data:hello", "--module", "com.example.hello");

        assertEquals(0, written.code(), written.err());
    }

    @Test
    void aModuleInTheLanguagesOwnNamespaceIsRefused(@TempDir Path directory) {
        Run run = run(directory, "com.example:hello", "--module", "souther.hello");

        assertEquals(2, run.code());
        assertTrue(run.err().contains("souther.hello"), run.err());
    }

    @Test
    void aValueAnOptionDoesNotHaveIsRefusedWithTheValuesItHas(@TempDir Path directory) {
        Run build = run(directory, "com.example:hello", "--build", "bazel");
        Run model = run(directory, "com.example:hello", "--model", "everything");

        assertEquals(2, build.code());
        assertTrue(build.err().contains("maven, gradle"), build.err());
        assertEquals(2, model.code());
        assertTrue(model.err().contains("none, minimal, full"), model.err());
    }

    /**
     * A compiler with no version of its own writes no build file.
     *
     * <p>What a build file names has to resolve. Running from class files there is no manifest and
     * no release to name, and a pom naming the word this compiler falls back to would be a project
     * that cannot be built and a line nobody knows how to correct.
     */
    @Test
    void aCompilerWithNoVersionWritesNoBuildFile(@TempDir Path directory) throws IOException {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();

        int code = InitCommand.run(new String[] {"com.example:hello"}, Locale.ENGLISH,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8), directory, null);

        assertEquals(2, code);
        assertEquals(List.of(), Files.list(directory).toList());
    }

    private static final String POM = """
            <project>
              <groupId>com.acme</groupId>
              <artifactId>billing</artifactId>
            </project>
            """;

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
