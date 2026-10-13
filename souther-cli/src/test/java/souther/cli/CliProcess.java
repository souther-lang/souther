package souther.cli;

import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The CLI run as a process of its own, for what is a fact about a process: arguments, standard
 * streams, the working directory, the environment and the exit status.
 *
 * <p>Nothing about the process is left to the machine running the test. It inherits only what
 * starting a process needs from the environment, its home is {@link #userHome} under the test's
 * own directory — so the directory a fetched backend goes to where {@code SOUTHER_HOME} is unset
 * is never the home of whoever runs the test — and its standard streams are written in UTF-8,
 * which is what they are read in here, rather than in whatever the platform's locale makes them.
 * What it writes is kept under the test's directory too, and goes with it.
 */
final class CliProcess {

    private CliProcess() {}

    private static final Set<String> KEPT = Set.of("PATH", "SystemRoot", "TEMP", "TMP", "TMPDIR");

    record Ran(int code, String out, String err) {}

    /** The home a process run with {@code scratch} is given. */
    static Path userHome(Path scratch) {
        return scratch.resolve("user-home");
    }

    static Ran run(Path scratch, Path workingDirectory, Map<String, String> environment,
                   List<String> jvmProperties, String stdin, String... args) throws Exception {
        Path userHome = Files.createDirectories(userHome(scratch));
        Path streams = Files.createTempDirectory(Files.createDirectories(scratch.resolve("runs")),
                "run");
        List<String> command = new ArrayList<>();
        command.add(Path.of(System.getProperty("java.home"), "bin", "java").toString());
        command.add("-Duser.home=" + userHome);
        command.add("-Dstdout.encoding=UTF-8");
        command.add("-Dstderr.encoding=UTF-8");
        command.addAll(jvmProperties);
        command.addAll(List.of("-cp", System.getProperty("java.class.path"), "souther.cli.Main"));
        command.addAll(List.of(args));
        Path out = streams.resolve("out");
        Path err = streams.resolve("err");
        ProcessBuilder builder = new ProcessBuilder(command).directory(workingDirectory.toFile())
                .redirectOutput(out.toFile()).redirectError(err.toFile());
        // What a process needs to start and to find a temporary directory, and nothing else: a
        // variable the CLI reads, or comes to read, reaches it only where a test sets it.
        builder.environment().keySet().retainAll(KEPT);
        builder.environment().putAll(environment);
        Process process = builder.start();
        try (var in = process.getOutputStream()) {
            in.write(stdin.getBytes(StandardCharsets.UTF_8));
        }
        int code = process.waitFor();
        return new Ran(code, Files.readString(out, StandardCharsets.UTF_8),
                Files.readString(err, StandardCharsets.UTF_8));
    }
}
