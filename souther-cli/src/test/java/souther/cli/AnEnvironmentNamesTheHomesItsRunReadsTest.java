package souther.cli;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.ByteArrayInputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@link Environment} names the user's home and the JVM a backend is run on, or is not one.
 *
 * <p>A run reads both without asking whether they are there: where a fetched backend goes is under
 * the home, and a backend is started on the JVM. An environment without them is refused where it is
 * built, rather than being a run that fails with nothing named the first time one of them is read.
 */
class AnEnvironmentNamesTheHomesItsRunReadsTest {

    @TempDir
    Path dir;

    private static final List<String> NAMED = List.of("user.home", "java.home");

    private Environment withProperties(Map<String, String> properties) {
        PrintStream nowhere = new PrintStream(OutputStream.nullOutputStream());
        return new Environment(Map.of(), properties, dir, new ByteArrayInputStream(new byte[0]),
                nowhere, nowhere, false);
    }

    private Map<String, String> both() {
        return Map.of("user.home", dir.resolve("home").toString(),
                "java.home", dir.resolve("jdk").toString());
    }

    /** The control: with both named it is built, and answers with what they name. */
    @Test
    void anEnvironmentNamingBothIsBuilt() {
        Environment environment = withProperties(both());

        assertEquals(dir.resolve("home"), environment.userHome());
        assertEquals(dir.resolve("jdk"), environment.javaHome());
    }

    @Test
    void anEnvironmentMissingEitherIsRefusedWhereItIsBuilt() {
        for (String missing : NAMED) {
            Map<String, String> properties = new HashMap<>(both());
            properties.remove(missing);

            IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                    () -> withProperties(properties), missing);

            assertTrue(refused.getMessage().contains(missing), refused.getMessage());
        }
    }

    @Test
    void anEnvironmentNamingEitherAsNothingIsRefused() {
        for (String blank : NAMED) {
            Map<String, String> properties = new HashMap<>(both());
            properties.put(blank, " ");

            assertThrows(IllegalArgumentException.class, () -> withProperties(properties), blank);
        }
    }

    /** This process's is one: a JVM names both. */
    @Test
    void thisProcessNamesBoth() {
        Environment environment = Environment.ofThisProcess();

        assertEquals(Path.of(System.getProperty("user.home")), environment.userHome());
        assertEquals(Path.of(System.getProperty("java.home")), environment.javaHome());
    }
}
