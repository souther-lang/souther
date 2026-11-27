package souther.cli.backend;

import souther.compiler.command.TargetCommand;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.IOException;
import java.io.OutputStream;
import java.net.URISyntaxException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;

/**
 * A jar built inside a test, carrying the descriptor of a backend and a command it provides.
 *
 * <p>What the command does when run is to say what it was given — its arguments, the directory it
 * is run in, one environment variable and its input — on the output it was given, to say which
 * compiler it reached, to say something on the error output, and to answer with the status written
 * after {@code --exit}. A test reads that back through the CLI and so holds the CLI to handing
 * each of them over.
 *
 * <p>The marker is a file in the jar and not a constant in the class, so every jar holds the same
 * class and it is compiled once for the run. What tells two jars apart is what the class reads out
 * of the one it was loaded from, which is what a jar written with another marker would have said.
 */
public final class FakeBackend {

    private FakeBackend() {}

    /** Where in the jar the marker is written. */
    private static final String MARKER = "fake-backend-marker";

    /** Where a jar names the commands it provides. */
    private static final String PROVIDED = "META-INF/services/" + TargetCommand.class.getName();

    /** The class of the compiler a jar may carry a second definition of. */
    private static final String A_CLASS_OF_THE_COMPILER = "souther/compiler/meta/ModuleMetadata";

    /** What the second definition says the compiler's version is. */
    public static final String THE_JARS_OWN_COMPILER = "the-jar's-own";

    private static final String SOURCE = """
            import souther.compiler.command.Environment;
            import souther.compiler.command.TargetCommand;
            import souther.compiler.meta.ModuleMetadata;

            import java.io.IOException;
            import java.io.PrintStream;
            import java.io.UncheckedIOException;
            import java.util.List;

            public class Fake implements TargetCommand {
                @Override
                public int run(List<String> args, Environment environment) {
                    PrintStream out = environment.out();
                    try (var marker = Fake.class.getResourceAsStream("/%s")) {
                        out.println("marker=" + new String(marker.readAllBytes(), "UTF-8"));
                        out.println("args=" + String.join("|", args));
                        out.println("cwd=" + environment.workingDirectory().toRealPath());
                        out.println("env=" + environment.variable("FAKE_ENV"));
                        out.println("compiler=" + ModuleMetadata.compilerVersion());
                        out.println("stdin=" + new String(environment.in().readAllBytes()));
                    } catch (IOException e) {
                        throw new UncheckedIOException(e);
                    }
                    environment.err().println("said-on-stderr");
                    int status = 0;
                    for (int i = 0; i < args.size() - 1; i++) {
                        if (args.get(i).equals("--exit")) {
                            status = Integer.parseInt(args.get(i + 1));
                        }
                    }
                    return status;
                }
            }
            """;

    private static final String SECOND_DEFINITION = """
            package souther.compiler.meta;

            public final class ModuleMetadata {
                public static String compilerVersion() {
                    return "%s";
                }
            }
            """;

    /** Writes a backend jar at {@code jar}, whose output says {@code marker}. */
    public static Path write(Path jar, String name, String southerVersion, String marker)
            throws IOException {
        return pack(jar, marker, descriptor(name, southerVersion), "Fake\n", false);
    }

    /** Writes a jar at {@code jar} whose descriptor is exactly {@code descriptor}, or none. */
    public static Path writeWithDescriptor(Path jar, String descriptor) throws IOException {
        return pack(jar, "described", descriptor, "Fake\n", false);
    }

    /**
     * Writes a backend jar at {@code jar} that names the commands it provides as {@code provided}
     * says, one class to a line, or names none where that is null.
     */
    public static Path writeProviding(Path jar, String name, String southerVersion,
                                      String provided) throws IOException {
        return pack(jar, "providing", descriptor(name, southerVersion), provided, false);
    }

    /**
     * Writes a backend jar at {@code jar} that also holds a class under a name of the compiler's,
     * which answers {@link #THE_JARS_OWN_COMPILER} where the compiler's answers its version.
     */
    public static Path writeCarryingAClassOfTheCompiler(Path jar, String name,
                                                        String southerVersion) throws IOException {
        return pack(jar, "carrying", descriptor(name, southerVersion), "Fake\n", true);
    }

    private static String descriptor(String name, String southerVersion) {
        return "name=" + name + "\nsouther.version=" + southerVersion + "\n";
    }

    /** Where the two classes were compiled to, the first time a jar is asked for. */
    private static Path compiledTo;

    private static synchronized Path compiled() throws IOException {
        if (compiledTo == null) {
            Path work = Files.createTempDirectory("fake-backend");
            Path source = work.resolve("Fake.java");
            Files.writeString(source, SOURCE.formatted(MARKER));
            Path second = work.resolve("ModuleMetadata.java");
            Files.writeString(second, SECOND_DEFINITION.formatted(THE_JARS_OWN_COMPILER));
            // The command is compiled against the compiler this test runs with, and the second
            // definition on its own, so the command is not compiled against it.
            JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
            if (compiler.run(null, null, null, "-classpath", theCompiler(), "-d",
                    work.toString(), source.toString()) != 0
                    || compiler.run(null, null, null, "-d", work.toString(),
                    second.toString()) != 0) {
                throw new IllegalStateException("the fake backend did not compile");
            }
            compiledTo = work;
        }
        return compiledTo;
    }

    /** Where the compiler this test runs with was loaded from. */
    private static String theCompiler() {
        try {
            return Path.of(TargetCommand.class.getProtectionDomain().getCodeSource().getLocation()
                    .toURI()).toString();
        } catch (URISyntaxException e) {
            throw new IllegalStateException(e);
        }
    }

    private static Path pack(Path jar, String marker, String descriptor, String provided,
                             boolean carryingAClassOfTheCompiler) throws IOException {
        Path classes = compiled();
        Files.createDirectories(jar.getParent());
        try (OutputStream file = Files.newOutputStream(jar);
             JarOutputStream out = new JarOutputStream(file)) {
            entry(out, "Fake.class", Files.readAllBytes(classes.resolve("Fake.class")));
            entry(out, MARKER, marker.getBytes(StandardCharsets.UTF_8));
            if (descriptor != null) {
                entry(out, Backends.DESCRIPTOR, descriptor.getBytes(StandardCharsets.ISO_8859_1));
            }
            if (provided != null) {
                entry(out, PROVIDED, provided.getBytes(StandardCharsets.UTF_8));
            }
            if (carryingAClassOfTheCompiler) {
                entry(out, A_CLASS_OF_THE_COMPILER + ".class", Files.readAllBytes(
                        classes.resolve(A_CLASS_OF_THE_COMPILER + ".class")));
            }
        }
        return jar;
    }

    private static void entry(JarOutputStream out, String name, byte[] bytes) throws IOException {
        out.putNextEntry(new JarEntry(name));
        out.write(bytes);
        out.closeEntry();
    }
}
