package souther.cli;

import org.junit.jupiter.api.Test;
import souther.lsp.ToolingMetadata;
import souther.test.RepositoryLayout;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The stack a launcher gives the JVM, and the Java it refuses to run below, are the root pom's, and
 * no launcher states either of its own.
 *
 * <p>The stack is what holds the bound on what a definition may say
 * ([#source-structural-complexity-is-bounded]): every phase descends what it builds by recursion,
 * and a source at the bound needs about a megabyte, which is more than a platform's default on some
 * of the platforms this runs on. A launcher that gave the JVM less would refuse a source the
 * compiler supports, and would refuse it only where that launcher is the one in use.
 *
 * <p>Each distribution reaches the JVM through a launcher of its own, and each takes the value from
 * the build rather than agreeing with the others by hand. The two scripts are filtered when they are
 * packaged, so what is asked of them is that every place they hand the value over names the
 * property, and that the root pom states it. The Windows packaging runs outside the build, so it
 * reads the JVM arguments out of the jar it packages, from the tooling metadata every client reads.
 *
 * <p>What a comment says about the flag is not the flag, so comments are dropped before anything is
 * read out.
 */
class EveryLauncherTakesWhatItGivesTheJvmFromTheBuildTest {

    private static final Pattern STACK = Pattern.compile("-Xss(\\S+)");
    private static final Pattern MINIMUM = Pattern.compile("LSS (\\S+)");
    /** A Java named by a number where the launcher says what it needs, as in "a JDK 25". */
    private static final Pattern A_JAVA_BY_NUMBER = Pattern.compile("(?:Java|JDK) (\\d+)");
    private static final Pattern COMMENT = Pattern.compile("^\\s*(#|rem\\s|rem$).*", Pattern.CASE_INSENSITIVE);

    private static final RepositoryLayout LAYOUT = RepositoryLayout.ofWorkingDirectory();

    @Test
    void theScriptsHandTheJvmTheStackTheRootPomStates() throws Exception {
        assertFalse(LAYOUT.rootProperty("souther.jvm.stack").isBlank());
        for (String launcher : List.of("souther", "souther.cmd")) {
            List<String> given = read(launcher(launcher), STACK);

            assertFalse(given.isEmpty(), launcher + " gives the JVM no stack outside its comments,"
                    + " so a source at the supported bound is refused wherever it is the launcher"
                    + " in use");
            for (String stack : given) {
                assertEquals("@souther.jvm.stack@", stack, launcher + " states a stack of its own");
            }
        }
    }

    @Test
    void theBatchLauncherRefusesTheJavaTheRootPomStates() throws Exception {
        assertFalse(LAYOUT.rootProperty("souther.java.minimum").isBlank());
        List<String> compared = read(launcher("souther.cmd"), MINIMUM);

        assertFalse(compared.isEmpty(), "souther.cmd compares the Java it found with nothing");
        for (String minimum : compared) {
            assertEquals("@souther.java.minimum@", minimum, "souther.cmd states a Java of its own");
        }
        assertEquals(List.of(), read(launcher("souther.cmd"), A_JAVA_BY_NUMBER),
                "souther.cmd tells its reader of a Java by a number of its own");
    }

    @Test
    void theWindowsImageTakesItsJvmArgumentsFromTheJar() throws Exception {
        Path packaging = LAYOUT.root().resolve("bin/package-windows.ps1");
        String script = Files.readString(packaging);

        assertEquals(List.of(), read(packaging, STACK), "the packaging states a stack of its own");
        assertTrue(script.contains(ToolingMetadata.RESOURCE) && script.contains("requiredJvmArgs"),
                "the packaging reads the JVM arguments from " + ToolingMetadata.RESOURCE);
    }

    private static Path launcher(String name) {
        Path launcher = LAYOUT.moduleNamed("souther-cli").resolve("src/main/launcher").resolve(name);
        assertTrue(Files.isRegularFile(launcher), launcher + " is where a launcher is written");
        return launcher;
    }

    /** What {@code pattern} captures on every line of {@code file} that is not a comment. */
    private static List<String> read(Path file, Pattern pattern) throws Exception {
        List<String> found = new ArrayList<>();
        for (String line : Files.readString(file).split("\\R")) {
            if (COMMENT.matcher(line).matches()) {
                continue;
            }
            Matcher said = pattern.matcher(line);
            while (said.find()) {
                found.add(said.group(1));
            }
        }
        return found;
    }
}
