package souther.cli;

import souther.cli.CliProcess.Ran;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

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
        Map<String, String> given = new HashMap<>();
        given.put("user.home", CliProcess.userHome(scratch).toString());
        given.put("java.home", System.getProperty("java.home"));
        given.putAll(properties);
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        Environment environment = new Environment(variables, given, workingDirectory,
                new ByteArrayInputStream(stdin.getBytes(StandardCharsets.UTF_8)),
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8), false);
        int code = Main.run(args, environment);
        return new Ran(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }

    /** Run in {@code scratch}, with these variables, no property of its own and no input. */
    static Ran run(Path scratch, Map<String, String> variables, String... args) {
        return run(scratch, scratch, variables, Map.of(), "", args);
    }
}
