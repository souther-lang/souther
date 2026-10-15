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
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code souther init --build none} starts a project that has no Java build. With no build file,
 * nothing else says which Souther the project's direct use requires, so the one file it writes
 * beside the sources is {@code .souther-version}.
 */
class InitWithNoBuildWritesTheSourcesAndTheVersionFileAndNothingElseTest {

    private record Run(int code, String out, String err) {}

    private static Run run(Path here, String souther, String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = InitCommand.run(args, Locale.ENGLISH,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8), here, souther);
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }

    private static Path project(Path parent, String name) throws IOException {
        return Files.createDirectories(parent.resolve(name));
    }

    private static java.util.List<String> written(Path root) throws IOException {
        try (Stream<Path> files = Files.walk(root)) {
            return files.filter(Files::isRegularFile)
                    .map(file -> root.relativize(file).toString()).sorted().toList();
        }
    }

    @Test
    void theSourcesAndTheVersionFileAreWrittenInTheDirectoryAndNoBuild(@TempDir Path parent)
            throws IOException {
        Path project = project(parent, "my-app");

        Run run = run(project, "9.9.9", "--build", "none");

        assertEquals(0, run.code(), run.err());
        assertEquals(java.util.List.of(".souther-version", "src/main/souther/my_app.sou"),
                written(project));
        assertEquals("9.9.9\n", Files.readString(project.resolve(".souther-version")));
        assertTrue(Files.readString(project.resolve("src/main/souther/my_app.sou"))
                .contains("module my_app"));
    }

    @Test
    void whatItSaysToRunNextNamesNoTarget(@TempDir Path parent) throws IOException {
        Path project = project(parent, "shop");

        Run run = run(project, "9.9.9", "--build", "none");

        assertTrue(run.out().contains("souther compile --target <target> <arguments>..."),
                run.out());
        assertFalse(run.out().contains("mvn"), run.out());
        assertFalse(run.out().contains("gradle"), run.out());
    }

    @Test
    void theModuleIsWhatTheLineWritesWhereItWritesOne(@TempDir Path parent) throws IOException {
        Path project = project(parent, "my-app");

        Run run = run(project, "9.9.9", "--build", "none", "--module", "com.acme.billing");

        assertEquals(0, run.code(), run.err());
        assertTrue(Files.readString(project.resolve("src/main/souther/billing.sou"))
                .contains("module com.acme.billing"));
    }

    @Test
    void theDirectoryTheLineNamesIsTheProject(@TempDir Path parent) throws IOException {
        Path elsewhere = parent.resolve("elsewhere");

        Run run = run(parent, "9.9.9", "--build", "none", "-d", elsewhere.toString());

        assertEquals(0, run.code(), run.err());
        assertTrue(Files.isRegularFile(elsewhere.resolve(".souther-version")));
        assertTrue(Files.isRegularFile(elsewhere.resolve("src/main/souther/elsewhere.sou")));
        assertFalse(Files.exists(parent.resolve(".souther-version")));
    }

    @Test
    void aVersionFileThatIsThereIsLeftAsItIs(@TempDir Path parent) throws IOException {
        Path project = project(parent, "shop");
        Files.writeString(project.resolve(".souther-version"), "0.0.1\n");

        Run run = run(project, "9.9.9", "--build", "none");

        assertEquals(0, run.code(), run.err());
        assertEquals("0.0.1\n", Files.readString(project.resolve(".souther-version")));
        assertTrue(run.out().contains("kept"), run.out());
    }

    @Test
    void aCoordinateIsRefusedAndNothingIsWritten(@TempDir Path parent) throws IOException {
        Path project = project(parent, "shop");

        Run run = run(project, "9.9.9", "--build", "none", "com.example:shop");

        assertEquals(2, run.code());
        assertTrue(run.err().contains("com.example:shop"), run.err());
        assertEquals(java.util.List.of(), written(project));
    }

    @Test
    void aDirectoryThatIsNotAModuleNameIsRefusedAndAskedForOne(@TempDir Path parent)
            throws IOException {
        for (String name : new String[] {"my.app", "2fast", "_x"}) {
            Path project = project(parent, name);

            Run run = run(project, "9.9.9", "--build", "none");

            assertEquals(2, run.code(), name + ": " + run.err());
            assertTrue(run.err().contains("--module"), name + ": " + run.err());
            assertEquals(java.util.List.of(), written(project), name);
        }
    }

    @Test
    void aModuleNameThatIsReservedIsRefusedAsItIsWithABuild(@TempDir Path parent)
            throws IOException {
        Path project = project(parent, "shop");

        Run run = run(project, "9.9.9", "--build", "none", "--module", "souther.shop");

        assertEquals(2, run.code(), run.out());
        assertEquals(java.util.List.of(), written(project));
    }

    @Test
    void whereABuildIsAlreadyThereTheBuildDecidesAndNoneIsRefused(@TempDir Path parent)
            throws IOException {
        Path project = project(parent, "shop");
        Files.writeString(project.resolve("pom.xml"), """
                <project>
                  <groupId>com.acme</groupId>
                  <artifactId>shop</artifactId>
                </project>
                """);

        Run run = run(project, "9.9.9", "--build", "none");

        assertEquals(2, run.code(), run.out());
        assertFalse(Files.exists(project.resolve(".souther-version")));
    }

    @Test
    void aSoutherWithNoVersionHasNothingToWriteAndRefuses(@TempDir Path parent)
            throws IOException {
        Path project = project(parent, "shop");

        Run run = run(project, null, "--build", "none");

        assertEquals(2, run.code());
        assertEquals(java.util.List.of(), written(project));
    }

    @Test
    void aBuildThatIsWrittenStillWritesNoVersionFileAndMavenIsStillTheDefault(
            @TempDir Path parent) throws IOException {
        Run run = run(parent, "9.9.9", "com.example:hello");

        assertEquals(0, run.code(), run.err());
        assertTrue(Files.isRegularFile(parent.resolve("hello/pom.xml")));
        assertFalse(Files.exists(parent.resolve("hello/.souther-version")));
    }
}
