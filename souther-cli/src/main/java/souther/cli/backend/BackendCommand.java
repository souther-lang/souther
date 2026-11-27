package souther.cli.backend;

import souther.compiler.command.Environment;
import souther.compiler.command.TargetCommand;

import java.io.IOException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.List;
import java.util.ServiceConfigurationError;
import java.util.ServiceLoader;
import java.util.jar.Attributes;
import java.util.jar.JarFile;
import java.util.jar.Manifest;

/**
 * Runs the command a backend provides, in this JVM.
 *
 * <p>A backend is one jar, and three things follow from that, each held here and nowhere else.
 *
 * <p>What is loaded for it is the jar's or this Souther's. The jar is read by a loader of its own
 * whose parent is the one that loaded this Souther, and a class both hold is the parent's, so the
 * compiler the backend reads a program with is this Souther's whatever the jar carries. The loader
 * reads the jar and nothing beside it: a manifest that names a {@code Class-Path} would have it
 * read other jars as the backend's own, so a jar with one is refused. The command is then the one
 * {@link TargetCommand} that loader defines, which is the one the jar holds: a provider the parent
 * defines is not the jar's, and a jar with none of its own, or with more than one, is refused
 * before any is constructed.
 *
 * <p>Everything of the jar's runs in one place. The loader is the thread's context loader from
 * before the first class of the jar is linked until the command has answered or thrown, so a
 * lookup the backend makes without naming a loader finds what its jar holds, whether it makes it
 * in a static initializer, in its constructor or while it runs.
 *
 * <p>Until the command is called, whatever goes wrong is the jar not being a backend that can be
 * run, and is a refusal that names the jar: a class that does not link, a provider that is no
 * command, a constructor that throws. Once it is called the run is the command's: the arguments
 * and the environment pass through unchanged, what it throws is thrown on as it is, and what it
 * answers is the answer, which letting go of the loader afterwards does not change.
 */
public final class BackendCommand {

    private BackendCommand() {}

    /**
     * Runs the backend's command with {@code arguments} in {@code environment}, answering with its
     * exit status.
     *
     * @throws Backends.Refused where the jar cannot be read, names a class path beside itself,
     *         does not provide exactly one command of its own, or provides one that cannot be made
     */
    public static int run(Backends.Backend backend, List<String> arguments, Environment environment)
            throws Backends.Refused {
        Thread thread = Thread.currentThread();
        ClassLoader before = thread.getContextClassLoader();
        URLClassLoader loader = readingOnly(backend);
        thread.setContextClassLoader(loader);
        try {
            return provided(backend, loader).run(arguments, environment);
        } finally {
            thread.setContextClassLoader(before);
            letGo(loader);
        }
    }

    /**
     * A loader that reads the backend's jar and nothing beside it, under this Souther's own. The
     * manifest's {@code Class-Path} is the one way a jar has of adding to what its loader reads.
     */
    private static URLClassLoader readingOnly(Backends.Backend backend) throws Backends.Refused {
        try {
            try (JarFile jar = new JarFile(backend.jar().toFile())) {
                Manifest manifest = jar.getManifest();
                if (manifest != null
                        && manifest.getMainAttributes().getValue(Attributes.Name.CLASS_PATH) != null) {
                    throw new Backends.Refused("cli.backend.classpath", backend.jar());
                }
            }
            return new URLClassLoader(new URL[] {backend.jar().toUri().toURL()},
                    TargetCommand.class.getClassLoader());
        } catch (IOException e) {
            throw new Backends.Refused("cli.backend.command.unusable", backend.jar(), why(e));
        }
    }

    /**
     * The one command {@code loader} defines, constructed.
     *
     * <p>Counted before any is constructed, so a jar providing two runs neither. What stops a
     * command being found or made is not one kind of throwable: the lookup says a provider is no
     * command or could not be constructed, the JVM says a class does not link, whether for a
     * class it extends that is nowhere or for a class file newer than this JVM reads, and a
     * loader says a class may not be defined. Each is the jar's, and none is this command's to
     * die of.
     */
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
        } catch (ServiceConfigurationError | LinkageError | RuntimeException e) {
            throw new Backends.Refused("cli.backend.command.unusable", backend.jar(), why(e));
        }
    }

    /**
     * What {@code thrown} says and what each thing that caused it says. Which of them names what
     * is wrong with the jar depends on the JDK: one hands on the JVM's own error for a class that
     * does not link, another wraps it in the lookup's and says only that the provider was not
     * found.
     */
    private static String why(Throwable thrown) {
        StringBuilder said = new StringBuilder(thrown.toString());
        for (Throwable cause = thrown.getCause(); cause != null; cause = cause.getCause()) {
            said.append(": ").append(cause);
        }
        return said.toString();
    }

    /**
     * Closes the loader. That it could not be closed changes nothing the command did or answered,
     * and nothing reads through it again, so it is not a failure of the run.
     */
    private static void letGo(URLClassLoader loader) {
        try {
            loader.close();
        } catch (IOException _) {
            // The command has answered or thrown, and that is what the run comes to.
        }
    }
}
