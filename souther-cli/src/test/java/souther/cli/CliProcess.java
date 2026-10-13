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
 * <p>The process is given a home of its own, so the directory a fetched backend goes to where
 * {@code SOUTHER_HOME} is unset is never the home of whoever runs the test, and inherits none of
 * that person's environment beyond what starting a process needs.
 */
final class CliProcess {

    private CliProcess() {}

    private static final Set<String> KEPT = Set.of("PATH", "SystemRoot", "TEMP", "TMP", "TMPDIR");

    record Ran(int code, String out, String err) {}

    static Ran run(Path workingDirectory, Map<String, String> environment,
                   List<String> jvmProperties, String stdin, String... args) throws Exception {
        Path userHome = Files.createTempDirectory("user-home");
        List<String> command = new ArrayList<>();
        command.add(Path.of(System.getProperty("java.home"), "bin", "java").toString());
        command.add("-Duser.home=" + userHome);
        command.addAll(jvmProperties);
        command.addAll(List.of("-cp", System.getProperty("java.class.path"), "souther.cli.Main"));
        command.addAll(List.of(args));
        Path out = Files.createTempFile("cli", ".out");
        Path err = Files.createTempFile("cli", ".err");
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
        return new Ran(code, Files.readString(out), Files.readString(err));
    }
}
