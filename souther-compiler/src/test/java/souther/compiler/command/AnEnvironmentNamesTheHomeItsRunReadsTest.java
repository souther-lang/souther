package souther.compiler.command;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;
import souther.test.WrittenOn;

import java.io.ByteArrayInputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.file.Path;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@link Environment} names the user's home, or is not one.
 *
 * <p>A run reads it without asking whether it is there: where a fetched backend goes is under the
 * home. An environment without it is refused where it is built, rather than being a run that fails
 * with nothing named the first time it is read.
 */
class AnEnvironmentNamesTheHomeItsRunReadsTest {

    @TempDir
    Path dir;

    private Environment withProperties(Map<String, String> properties) {
        PrintStream nowhere = new PrintStream(OutputStream.nullOutputStream());
        return new Environment(Map.of(), properties, dir, new ByteArrayInputStream(new byte[0]),
                nowhere, nowhere, false, WrittenOn.DAY);
    }

    /** The control: with the home named it is built, and answers with what it names. */
    @Test
    void anEnvironmentNamingTheHomeIsBuilt() {
        Environment environment = withProperties(
                Map.of("user.home", dir.resolve("home").toString()));

        assertEquals(dir.resolve("home"), environment.userHome());
    }

    @Test
    void anEnvironmentMissingTheHomeIsRefusedWhereItIsBuilt() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> withProperties(Map.of()));

        assertTrue(refused.getMessage().contains("user.home"), refused.getMessage());
    }

    @Test
    void anEnvironmentNamingTheHomeAsNothingIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> withProperties(Map.of("user.home", " ")));
    }

    /** This process's is one: a JVM names its user's home. */
    @Test
    void thisProcessNamesTheHome() {
        Environment environment = Environment.ofThisProcess();

        assertEquals(Path.of(System.getProperty("user.home")), environment.userHome());
    }
}
