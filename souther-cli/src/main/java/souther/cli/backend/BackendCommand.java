package souther.cli.backend;

import souther.compiler.command.Environment;
import souther.compiler.command.TargetCommand;

import java.io.IOException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.List;
import java.util.ServiceConfigurationError;
import java.util.ServiceLoader;

/**
 * Runs the command a backend provides, in this JVM.
 *
 * <p>The jar is loaded by a loader of its own whose parent is the one that loaded this Souther. A
 * class both hold is the parent's, so the compiler the backend reads a program with is this
 * Souther's whatever the jar carries. The command is the one {@link TargetCommand} the jar itself
 * provides: a provider the parent defines is not the jar's, and a jar with none of its own, or
 * with more than one, is refused before anything of it runs.
 *
 * <p>What the command is handed passes through unchanged — the arguments, and the environment the
 * run was given — and what this answers with is what the command answered. Nothing here reads the
 * backend's options or its output. The loader is the thread's context loader while the command
 * runs, so a lookup the backend makes without naming a loader finds what its jar holds, and it is
 * closed when the command has answered.
 */
public final class BackendCommand {

    private BackendCommand() {}

    /**
     * Runs the backend's command with {@code arguments} in {@code environment}, answering with its
     * exit status.
     *
     * @throws Backends.Refused where the jar does not provide exactly one command of its own, or
     *         the one it provides cannot be loaded
     */
    public static int run(Backends.Backend backend, List<String> arguments, Environment environment)
            throws Backends.Refused, IOException {
        URL[] jar = {backend.jar().toUri().toURL()};
        Thread thread = Thread.currentThread();
        ClassLoader before = thread.getContextClassLoader();
        try (URLClassLoader loader = new URLClassLoader(jar,
                TargetCommand.class.getClassLoader())) {
            TargetCommand command = provided(backend, loader);
            thread.setContextClassLoader(loader);
            try {
                return command.run(arguments, environment);
            } finally {
                thread.setContextClassLoader(before);
            }
        }
    }

    /** The one command the classes of {@code loader}'s own jar provide. */
    private static TargetCommand provided(Backends.Backend backend, ClassLoader loader)
            throws Backends.Refused {
        try {
            List<ServiceLoader.Provider<TargetCommand>> own =
                    ServiceLoader.load(TargetCommand.class, loader).stream()
                            .filter(provider -> provider.type().getClassLoader() == loader)
                            .toList();
            if (own.size() != 1) {
                throw new Backends.Refused("cli.backend.command", backend.jar(), own.size());
            }
            return own.getFirst().get();
        } catch (ServiceConfigurationError e) {
            throw new Backends.Refused("cli.backend.command.unusable", backend.jar(),
                    e.getMessage());
        }
    }
}
