package souther.cli.backend;

import souther.cli.Environment;
import souther.lsp.ToolingMetadata;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;

/**
 * Runs a backend as a process of its own.
 *
 * <p>The JVM is the run's — the {@code java.home} it is given — and the arguments it is given are
 * the ones this Souther requires of a JVM, since the backend runs the same front end. What the
 * backend is handed passes through unchanged, as do the working directory, the environment and the
 * three standard streams, and what this answers with is the backend's exit status. Nothing here
 * reads the backend's options or its output.
 *
 * <p>The streams are inherited where the run's are the process's own, so a backend writing to a
 * terminal writes to the one the run was started on. Where they are not, the backend is given pipes
 * and what passes through them is copied to and from the run's streams, whole, before this answers.
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

    /** Runs the backend in {@code environment} and waits for it, answering with its exit status. */
    public static int run(Backends.Backend backend, List<String> arguments, Environment environment)
            throws IOException, InterruptedException {
        List<String> command = command(Path.of(environment.property("java.home")),
                ToolingMetadata.requiredJvmArgs(), backend, arguments);
        ProcessBuilder builder = new ProcessBuilder(command)
                .directory(environment.workingDirectory().toAbsolutePath().toFile());
        builder.environment().clear();
        builder.environment().putAll(environment.variables());
        if (environment.processStreams()) {
            return builder.inheritIO().start().waitFor();
        }
        Process process = builder.start();
        Thread.ofVirtual().start(() -> handOver(environment.in(), process.getOutputStream()));
        try (ExecutorService copying = Executors.newVirtualThreadPerTaskExecutor()) {
            Future<Void> out = copying.submit(() -> copy(process.getInputStream(),
                    environment.out()));
            Future<Void> err = copying.submit(() -> copy(process.getErrorStream(),
                    environment.err()));
            int status = process.waitFor();
            finished(out);
            finished(err);
            return status;
        }
    }

    /** Everything {@code from} holds, written to {@code to}. */
    private static Void copy(InputStream from, OutputStream to) throws IOException {
        from.transferTo(to);
        to.flush();
        return null;
    }

    /**
     * The run's input, handed to the backend and then closed, so the backend reads to its end.
     *
     * <p>Not waited for. A backend may end without reading its input, and the pipe it leaves
     * refuses what is still being written; that is the backend having taken all it wanted, and not
     * something to say.
     */
    private static void handOver(InputStream from, OutputStream to) {
        try (to) {
            from.transferTo(to);
        } catch (IOException _) {
            // The backend closed its end; it has what it read.
        }
    }

    private static void finished(Future<Void> copied) throws IOException, InterruptedException {
        try {
            copied.get();
        } catch (ExecutionException e) {
            throw e.getCause() instanceof IOException io ? io : new IOException(e.getCause());
        }
    }
}
