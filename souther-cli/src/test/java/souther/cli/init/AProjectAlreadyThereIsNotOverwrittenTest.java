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
 * Running this command again finishes what a run left, and touches nothing else.
 *
 * <p>Asked by writing each file first and reading it back afterwards, rather than by running the
 * command twice. A second run over what the first wrote would compare this command's output with its
 * own, and would pass just as well if it overwrote every file with the same text; what a reader has
 * in that directory is their own work.
 */
class AProjectAlreadyThereIsNotOverwrittenTest {

    @Test
    void whatIsAlreadyWrittenIsLeftAndSaidToHaveBeen(@TempDir Path directory) throws IOException {
        Path project = directory.resolve("hello");
        Path model = project.resolve("src/main/souther/hello.sou");
        Files.createDirectories(model.getParent());
        Files.writeString(model, "module com.example.hello\n\n// mine\n");
        Files.writeString(project.resolve("pom.xml"), "<project>mine</project>");

        Run run = run(directory, "com.example:hello");

        assertEquals(0, run.code());
        assertEquals("module com.example.hello\n\n// mine\n", Files.readString(model),
                "a model somebody had begun was written over");
        assertEquals("<project>mine</project>", Files.readString(project.resolve("pom.xml")));
        assertTrue(run.out().contains("kept     hello/pom.xml"),
                "a file that was left alone is not reported as left alone:\n" + run.out());
        assertTrue(run.out().contains("created  hello/src/main/souther/hello.examples.sou"),
                "the rest of the project was not finished:\n" + run.out());
    }

    /** A directory with nothing in it gets the whole project, and is told what it got. */
    @Test
    void anEmptyDirectoryGetsTheWholeProject(@TempDir Path directory) throws IOException {
        Run run = run(directory, "com.example:hello");

        assertEquals(0, run.code());
        for (String file : List.of("pom.xml", ".gitignore", "src/main/souther/hello.sou",
                "src/main/souther/hello.examples.sou",
                "src/test/java/com/example/hello/ReturnBookTest.java")) {
            assertTrue(Files.isRegularFile(directory.resolve("hello").resolve(file)),
                    "not written: " + file);
        }
        assertTrue(run.out().contains("module com.example.hello"),
                "the module name, which is derived and not written by the author, is not said:\n"
                        + run.out());
    }

    /**
     * A build file is not written at all where a project is only being added to.
     *
     * <p>The one thing that separates the two readings of this command: in a directory of its own it
     * lays out a project, and in somebody's project it adds a model to what they have.
     */
    @Test
    void addingToABuildWritesNoBuildFile(@TempDir Path directory) throws IOException {
        Files.writeString(directory.resolve("pom.xml"), """
                <project>
                  <groupId>com.acme</groupId>
                  <artifactId>billing</artifactId>
                </project>
                """);

        Run run = run(directory);

        assertEquals(0, run.code(), run.err());
        assertTrue(Files.isRegularFile(directory.resolve("src/main/souther/billing.sou")));
        assertTrue(Files.notExists(directory.resolve("src/test")),
                "adding to a build wrote a test into somebody else's project");
        assertTrue(run.out().contains("read"), run.out());
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
