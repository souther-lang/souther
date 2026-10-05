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
 */
public final class FakeBackend {

    private FakeBackend() {}

    private static final String SOURCE = """
            public class Fake {
                public static void main(String[] args) throws Exception {
                    System.out.println("marker=%s");
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
        Path work = Files.createTempDirectory("fake-backend");
        Path source = work.resolve("Fake.java");
        Files.writeString(source, SOURCE.formatted(marker));
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        if (compiler.run(null, null, null, "-d", work.toString(), source.toString()) != 0) {
            throw new IllegalStateException("the fake backend did not compile");
        }
        return pack(jar, work.resolve("Fake.class"), descriptor);
    }

    private static Path pack(Path jar, Path compiled, String descriptor) throws IOException {
        Manifest manifest = new Manifest();
        manifest.getMainAttributes().put(Attributes.Name.MANIFEST_VERSION, "1.0");
        manifest.getMainAttributes().put(Attributes.Name.MAIN_CLASS, "Fake");
        Files.createDirectories(jar.getParent());
        try (OutputStream file = Files.newOutputStream(jar);
             JarOutputStream out = new JarOutputStream(file, manifest)) {
            out.putNextEntry(new JarEntry("Fake.class"));
            out.write(Files.readAllBytes(compiled));
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
