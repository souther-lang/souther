package souther.cli.backend;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.IOException;
import java.io.OutputStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;

/**
 * An executable jar built inside a test, carrying the descriptor of a backend.
 *
 * <p>What it does when run is to say what it was given — its arguments, working directory, one
 * environment variable and standard input — on standard output, to say something on standard error,
 * and to exit with the status written after {@code --exit}. A test reads that back through the
 * CLI and so holds the CLI to passing each of them through.
 *
 * <p>The marker is a file in the jar and not a constant in the class, so every jar holds the same
 * class and it is compiled once for the run. What tells two jars apart is what the class reads out
 * of the one it was started from, which is what a jar written with another marker would have said.
 */
public final class FakeBackend {

    private FakeBackend() {}

    /** Where in the jar the marker is written. */
    private static final String MARKER = "fake-backend-marker";

    private static final String SOURCE = """
            public class Fake {
                public static void main(String[] args) throws Exception {
                    try (var marker = Fake.class.getResourceAsStream("/%s")) {
                        System.out.println("marker="
                                + new String(marker.readAllBytes(), "UTF-8"));
                    }
                    System.out.println("args=" + String.join("|", args));
                    System.out.println("cwd=" + System.getProperty("user.dir"));
                    System.out.println("env=" + System.getenv("FAKE_ENV"));
                    System.out.println("stdin=" + new String(System.in.readAllBytes()));
                    System.err.println("said-on-stderr");
                    int status = 0;
                    for (int i = 0; i < args.length - 1; i++) {
                        if (args[i].equals("--exit")) {
                            status = Integer.parseInt(args[i + 1]);
                        }
                    }
                    System.exit(status);
                }
            }
            """;

    /** Writes a backend jar at {@code jar}, whose output says {@code marker}. */
    public static Path write(Path jar, String name, String southerVersion, String marker)
            throws IOException {
        return build(jar, marker, "name=" + name + "\nsouther.version=" + southerVersion + "\n");
    }

    /** Writes a jar at {@code jar} whose descriptor is exactly {@code descriptor}, or none. */
    public static Path writeWithDescriptor(Path jar, String descriptor) throws IOException {
        return build(jar, "described", descriptor);
    }

    private static Path build(Path jar, String marker, String descriptor) throws IOException {
        return pack(jar, compiled(), marker, descriptor);
    }

    /** The class every jar holds, compiled the first time a jar is asked for. */
    private static byte[] compiledClass;

    private static synchronized byte[] compiled() throws IOException {
        if (compiledClass == null) {
            Path work = Files.createTempDirectory("fake-backend");
            Path source = work.resolve("Fake.java");
            Files.writeString(source, SOURCE.formatted(MARKER));
            JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
            if (compiler.run(null, null, null, "-d", work.toString(), source.toString()) != 0) {
                throw new IllegalStateException("the fake backend did not compile");
            }
            compiledClass = Files.readAllBytes(work.resolve("Fake.class"));
        }
        return compiledClass;
    }

    private static Path pack(Path jar, byte[] compiled, String marker, String descriptor)
            throws IOException {
        Manifest manifest = new Manifest();
        manifest.getMainAttributes().put(Attributes.Name.MANIFEST_VERSION, "1.0");
        manifest.getMainAttributes().put(Attributes.Name.MAIN_CLASS, "Fake");
        Files.createDirectories(jar.getParent());
        try (OutputStream file = Files.newOutputStream(jar);
             JarOutputStream out = new JarOutputStream(file, manifest)) {
            out.putNextEntry(new JarEntry("Fake.class"));
            out.write(compiled);
            out.closeEntry();
            out.putNextEntry(new JarEntry(MARKER));
            out.write(marker.getBytes(StandardCharsets.UTF_8));
            out.closeEntry();
            if (descriptor != null) {
                out.putNextEntry(new JarEntry(Backends.DESCRIPTOR));
                out.write(descriptor.getBytes(StandardCharsets.ISO_8859_1));
                out.closeEntry();
            }
        }
        return jar;
    }
}
