package souther.cli.backend;

import souther.lsp.ToolingMetadata;

import java.io.IOException;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

/**
 * Runs a backend as a process of its own.
 *
 * <p>The JVM is this one's — its {@code java.home} — and the arguments it is given are the ones
 * this Souther requires of a JVM, since the backend runs the same front end. What the backend is
 * handed passes through unchanged, as do the working directory, the environment and the three
 * standard streams, and what this answers with is the backend's exit status. Nothing here reads the
 * backend's options or its output.
 */
public final class BackendProcess {

    private BackendProcess() {}

    /** The command line that starts the backend with these arguments. */
    static List<String> command(Path javaHome, List<String> jvmArguments,
                                Backends.Backend backend, List<String> arguments) {
        List<String> command = new ArrayList<>();
        command.add(javaHome.resolve("bin").resolve("java").toString());
        command.addAll(jvmArguments);
        command.add("-jar");
        command.add(backend.jar().toString());
        command.addAll(arguments);
        return command;
    }

    /** Runs the backend and waits for it, answering with its exit status. */
    public static int run(Backends.Backend backend, List<String> arguments)
            throws IOException, InterruptedException {
        List<String> command = command(Path.of(System.getProperty("java.home")),
                ToolingMetadata.requiredJvmArgs(), backend, arguments);
        return new ProcessBuilder(command).inheritIO().start().waitFor();
    }
}
