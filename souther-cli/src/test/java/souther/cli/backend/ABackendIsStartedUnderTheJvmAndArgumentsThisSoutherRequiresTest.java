package souther.cli.backend;

import org.junit.jupiter.api.Test;
import souther.lsp.ToolingMetadata;

import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A backend runs the same front end this Souther does, so it is started on the stack the tooling
 * metadata says that front end needs, and that statement is read where it is made and not copied.
 */
class ABackendIsStartedUnderTheJvmAndArgumentsThisSoutherRequiresTest {

    @Test
    void theCommandIsTheJvmsJavaThenItsArgumentsThenTheJarThenTheBackendsOwn() {
        Backends.Backend backend = new Backends.Backend("wasm", "1", Path.of("/b/wasm.jar"));

        List<String> command = BackendProcess.command(Path.of("/jdk"), List.of("-Xss4m"), backend,
                List.of("--help", "m.sou"));

        assertEquals(List.of(Path.of("/jdk", "bin", "java").toString(), "-Xss4m", "-jar",
                Path.of("/b/wasm.jar").toString(), "--help", "m.sou"), command);
    }

    @Test
    void theArgumentsAreTheOnesTheToolingMetadataStates() {
        List<String> required = ToolingMetadata.requiredJvmArgs();

        assertFalse(required.isEmpty());
        assertTrue(required.stream().anyMatch(argument -> argument.matches("-Xss\\d+[kKmM]")),
                required.toString());
        assertTrue(ToolingMetadata.text().contains(required.get(0)), required.toString());
    }
}
