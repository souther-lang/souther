package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.cli.backend.LocalRepository;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@code compile --target} and {@code backend fetch} refuse from the line alone, or from the
 * project the line is run in, is refused before any directory a backend is installed in is looked
 * at and before any repository is asked. So it is asked of the CLI in this process: nothing here
 * reads the home or the environment a run is given, which is what a process would be for.
 */
class ALineATargetIsWrittenWrongOnIsRefusedBeforeAnythingIsLookedForTest {

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

    /**
     * {@code --target jvm} is read as the line without it, which {@code compile} then reads as it
     * always has: the JVM's grammar is chosen by what is written before the arguments and by
     * nothing in them.
     */
    @Test
    void theJvmTargetIsTheCompileThereAlwaysWas() {
        List<String> arguments = List.of("-d", "out", "m.sou");

        assertEquals(new CompileInvocation.Jvm(arguments), CompileInvocation.read(
                new String[] {"--target", "jvm", "-d", "out", "m.sou"}));
        assertEquals(new CompileInvocation.Jvm(arguments),
                CompileInvocation.read(arguments.toArray(String[]::new)));
    }

    @Test
    void aTargetWrittenWithNoNameIsRefused(@TempDir Path work) {
        Said bare = run(work, "compile", "--target");
        Said option = run(work, "compile", "--target", "--help");

        assertEquals(2, bare.code());
        assertEquals(2, option.code());
        assertTrue(bare.err().contains("--target"), bare.err());
    }

    @Test
    void theTargetIsReadOnlyAsTheFirstArgument(@TempDir Path work) {
        Said said = run(work, "compile", "a.sou", "--target", "jvm");

        assertEquals(2, said.code());
        assertTrue(said.err().contains("--target"), said.err());
    }

    @Test
    void theJvmTargetStillRefusesAnOptionTheJvmDoesNotHave(@TempDir Path work) {
        Said said = run(work, "compile", "--target", "jvm", "--component", "m.sou");

        assertEquals(2, said.code());
        assertTrue(said.err().contains("--component"), said.err());
    }

    @Test
    void aProjectNamingAnotherSoutherRefusesTheTargetToo(@TempDir Path work) throws Exception {
        Files.writeString(work.resolve(ProjectVersion.FILE), "0.0.1-other\n");

        Said said = run(work, "compile", "--target", "fake");

        assertEquals(2, said.code());
        assertEquals("", said.out());
        assertTrue(said.err().contains("0.0.1-other"), said.err());
    }

    /**
     * With the repository named here, so that a line read as a fetch would ask it rather than
     * the one a machine running this is set to.
     */
    @Test
    void theFetchCommandTakesFetchAndATargetAndNothingElse(@TempDir Path work) throws Exception {
        try (LocalRepository repository = LocalRepository.start()) {
            System.setProperty("souther.repository", repository.uri().toString());
            try {
                for (List<String> line : List.of(List.of("backend"), List.of("backend", "fetch"),
                        List.of("backend", "get", "wasm"), List.of("backend", "fetch", "wasm", "x"),
                        List.of("backend", "fetch", "jvm"))) {
                    Said said = run(work, line.toArray(String[]::new));

                    assertEquals(2, said.code(), line + said.err());
                    assertFalse(said.out().contains("wasm"), line + said.out());
                }
            } finally {
                System.clearProperty("souther.repository");
            }
            assertEquals(List.of(), repository.asked());
        }
    }
}
