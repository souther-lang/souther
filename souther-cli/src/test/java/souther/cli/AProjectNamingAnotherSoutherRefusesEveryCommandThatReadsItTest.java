package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.compiler.meta.ModuleMetadata;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.EnumSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code .souther-version} names the Souther a project's direct command-line use requires. A
 * command that is about a project is refused under one naming another version; a command that is
 * not is the same wherever it is run. Which commands are which is a fact of {@link CliCommand},
 * and what is held here is that the refusal follows it.
 */
class AProjectNamingAnotherSoutherRefusesEveryCommandThatReadsItTest {

    private static final String OTHER = "0.0.1-not-this-one";

    private record Said(int code, String err, String out) {}

    private static Said run(Path workingDirectory, String... args) {
        PrintStream originalErr = System.err;
        PrintStream originalOut = System.out;
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            int code = Main.dispatch(args, workingDirectory);
            return new Said(code, err.toString(StandardCharsets.UTF_8),
                    out.toString(StandardCharsets.UTF_8));
        } finally {
            System.setErr(originalErr);
            System.setOut(originalOut);
        }
    }

    private static void declare(Path directory, String content) throws IOException {
        Files.writeString(directory.resolve(ProjectVersion.FILE), content);
    }

    @Test
    void theCommandsAProjectConstrainsAreTheOnesThatReadItsSources() {
        Set<CliCommand> constrained = EnumSet.noneOf(CliCommand.class);
        for (CliCommand command : CliCommand.values()) {
            if (command.scope() == CliCommand.Scope.PROJECT) {
                constrained.add(command);
            }
        }

        assertEquals(EnumSet.of(CliCommand.COMPILE, CliCommand.RUN, CliCommand.FMT,
                CliCommand.EXAMPLES), constrained);
    }

    @Test
    void everyConstrainedCommandIsRefusedNamingBothVersions(@TempDir Path project)
            throws IOException {
        declare(project, OTHER + "\n");

        for (CliCommand command : CliCommand.values()) {
            if (command.scope() != CliCommand.Scope.PROJECT) {
                continue;
            }
            Said said = run(project, command.spelling(), "model.sou");

            assertEquals(2, said.code(), command.spelling() + ": " + said.err());
            assertEquals("", said.out(), command.spelling());
            assertTrue(said.err().contains(OTHER), command.spelling() + ": " + said.err());
            assertTrue(said.err().contains(ModuleMetadata.compilerVersion()),
                    command.spelling() + ": " + said.err());
        }
    }

    @Test
    void aCommandThatIsNotAboutAProjectIsNotRefused(@TempDir Path project) throws IOException {
        declare(project, OTHER + "\n");

        for (String command : new String[] {"help", "version", "tooling"}) {
            Said said = run(project, command);

            assertEquals(0, said.code(), command + ": " + said.err());
            assertFalse(said.err().contains(ProjectVersion.FILE), command + ": " + said.err());
        }
    }

    @Test
    void askingAConstrainedCommandWhatItTakesIsAnsweredNotRefused(@TempDir Path project)
            throws IOException {
        declare(project, OTHER + "\n");

        Said help = run(project, "compile", "--help");
        Said version = run(project, "compile", "--version");

        assertEquals(0, help.code(), help.err());
        assertTrue(help.out().contains("usage: souther compile"), help.out());
        assertEquals(0, version.code(), version.err());
        assertEquals(Main.version(), version.out().strip());
    }

    @Test
    void aFileNamingThisSoutherRefusesNothing(@TempDir Path project) throws IOException {
        declare(project, ModuleMetadata.compilerVersion() + "\n");

        Said said = run(project, "fmt", project.resolve("absent.sou").toString());

        assertFalse(said.err().contains(ProjectVersion.FILE), said.err());
    }

    @Test
    void theNearestFileWinsAndIsFoundFromBelow(@TempDir Path root) throws IOException {
        Path inner = Files.createDirectories(root.resolve("a/b"));
        declare(root, OTHER + "\n");
        Path file = inner.resolve("absent.sou");

        Said refused = run(inner, "fmt", file.toString());
        declare(root.resolve("a"), ModuleMetadata.compilerVersion() + "\n");
        Said accepted = run(inner, "fmt", file.toString());

        assertEquals(2, refused.code(), refused.err());
        assertTrue(refused.err().contains(root.resolve(ProjectVersion.FILE).toString()),
                refused.err());
        assertFalse(accepted.err().contains(ProjectVersion.FILE), accepted.err());
    }

    @Test
    void aFileThatIsNotOneVersionOnOneLineIsRefusedAndNotNormalisedIntoOne(@TempDir Path project)
            throws IOException {
        String here = ModuleMetadata.compilerVersion();
        for (String content : new String[] {"", "\n", "0.1.0\n0.2.0\n", "at least 0.1.0",
                " " + here + "\n", here + " \n", here + "\n\n", "\n" + here + "\n"}) {
            declare(project, content);

            Said said = run(project, "fmt", "model.sou");

            assertEquals(2, said.code(), "'" + content + "': " + said.err());
            assertTrue(said.err().contains(ProjectVersion.FILE), said.err());
        }
    }

    @Test
    void aLineEndingIsNotPartOfTheVersion(@TempDir Path project) throws IOException {
        String here = ModuleMetadata.compilerVersion();
        for (String content : new String[] {here, here + "\n", here + "\r\n"}) {
            declare(project, content);

            Said said = run(project, "fmt", project.resolve("absent.sou").toString());

            assertFalse(said.err().contains(ProjectVersion.FILE), "'" + content + "': " + said.err());
        }
    }

    @Test
    void aFileThatCannotBeReadIsSaidSoAndIsNotACompilerFault(@TempDir Path project)
            throws IOException {
        Files.createDirectory(project.resolve(ProjectVersion.FILE));

        Said said = run(project, "fmt", "model.sou");

        assertEquals(2, said.code(), said.err());
        assertTrue(said.err().contains(ProjectVersion.FILE), said.err());
        assertFalse(said.err().contains("internal compiler error"), said.err());
    }

    @Test
    void noFileIsNoConstraint(@TempDir Path project) {
        Said said = run(project, "fmt", project.resolve("absent.sou").toString());

        assertFalse(said.err().contains(ProjectVersion.FILE), said.err());
    }
}
