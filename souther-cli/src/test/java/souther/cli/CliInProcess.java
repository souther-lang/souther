package souther.cli;

import souther.cli.CliProcess.Ran;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The CLI run in this JVM, in an {@link Environment} the test names, for what the command line does
 * with its environment: the variables and properties it is given, the directory it is run in, and
 * what it writes and answers with.
 *
 * <p>Nothing of the JVM running the test is read. The variables are the ones a test names and no
 * others; the properties are those, over a {@code user.home} under the test's own directory and the
 * {@code java.home} a backend the run starts is run on; and the streams are the ones read back here.
 * The same arguments through {@link CliProcess} reach the same {@link Main#run}, from an
 * {@link Environment} its process read.
 */
final class CliInProcess {

    private CliInProcess() {}

    static Ran run(Path scratch, Path workingDirectory, Map<String, String> variables,
                   Map<String, String> properties, String stdin, String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        Environment environment = environment(scratch, workingDirectory, variables, properties,
                new ByteArrayInputStream(stdin.getBytes(StandardCharsets.UTF_8)), out, err);
        int code = Main.run(args, environment);
        return new Ran(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }

    /**
     * The environment a run in {@code scratch} is given, with no variable and no property of its
     * own, on streams the caller holds: for a test that talks to the run while it goes on, or hands
     * the environment to something below {@link Main}.
     */
    static Environment environment(Path scratch, InputStream in, OutputStream out, OutputStream err) {
        return environment(scratch, scratch, Map.of(), Map.of(), in, out, err);
    }

    private static Environment environment(Path scratch, Path workingDirectory,
                                           Map<String, String> variables,
                                           Map<String, String> properties, InputStream in,
                                           OutputStream out, OutputStream err) {
        Map<String, String> given = new HashMap<>();
        given.put("user.home", CliProcess.userHome(scratch).toString());
        given.put("java.home", System.getProperty("java.home"));
        given.putAll(properties);
        return new Environment(variables, given, workingDirectory, in,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8), false);
    }

    /** Run in {@code scratch}, with these variables, no property of its own and no input. */
    static Ran run(Path scratch, Map<String, String> variables, String... args) {
        return run(scratch, scratch, variables, Map.of(), "", args);
    }

    /**
     * Run in a directory of its own, with no variable, no property of its own and no input: what
     * the command line answers wherever it is run, whatever the person running the tests exported.
     * The directory is this method's, and is gone when it returns; a test that reads back what a run
     * wrote names the directory with {@link #run(Path, Map, String...)}.
     */
    static Ran run(String... args) {
        Path scratch;
        try {
            scratch = Files.createTempDirectory("souther-cli-in-process");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        try {
            return run(scratch, Map.of(), args);
        } finally {
            delete(scratch);
        }
    }

    /**
     * What a run in a directory of its own writes on stdout, for a test whose run is meant to
     * succeed: an exit code other than zero fails the test, with what the run wrote on stderr, so
     * a command that writes what is looked for and then fails is not read as having answered.
     */
    static String printed(String... args) {
        Ran ran = run(args);
        assertEquals(0, ran.code(), () -> "the run failed:\n" + ran.err());
        return ran.out();
    }

    private static void delete(Path root) {
        try (Stream<Path> walk = Files.walk(root)) {
            for (Path path : walk.sorted(Comparator.reverseOrder()).toList()) {
                Files.delete(path);
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
