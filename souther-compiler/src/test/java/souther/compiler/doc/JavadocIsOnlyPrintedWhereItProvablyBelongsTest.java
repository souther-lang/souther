package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Recovered documentation is worth having only because it is true of the member it is printed
 * against. Two ways of getting that wrong survive keying by name and parameter count: an overload
 * that is simply undocumented takes its namesake's, and a jar with no sources beside it takes
 * whatever the tool happens to carry for that name — which is another version of the library.
 */
class JavadocIsOnlyPrintedWhereItProvablyBelongsTest {

    private static Path jarOf(Path dir, String name, String... sources) throws Exception {
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        Path classes = Files.createDirectories(dir.resolve(name + "-classes"));
        String[] args = new String[sources.length + 2];
        args[0] = "-d";
        args[1] = classes.toString();
        System.arraycopy(sources, 0, args, 2, sources.length);
        assertEquals(0, javac.run(null, OutputStream.nullOutputStream(), OutputStream.nullOutputStream(), args));

        Path jar = dir.resolve(name + ".jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            try (Stream<Path> files = Files.walk(classes)) {
                for (Path f : files.filter(Files::isRegularFile).toList()) {
                    out.putNextEntry(new JarEntry(classes.relativize(f).toString()));
                    out.write(Files.readAllBytes(f));
                }
            }
        }
        return jar;
    }

    private static String api(String name, Path classPath) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        assertEquals(0, JapiCommand.run(new String[]{name, "-cp", classPath.toString()},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(OutputStream.nullOutputStream(), true, StandardCharsets.UTF_8)));
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void anUndocumentedOverloadDoesNotBorrowItsNamesakesParameterName() throws Exception {
        Path dir = Files.createTempDirectory("one-documented");
        Path src = dir.resolve("acme/Reader.java");
        Files.createDirectories(src.getParent());
        Files.writeString(src, """
                package acme;

                /** Reads things. */
                public final class Reader {

                    /**
                     * Reads from text.
                     *
                     * @param text the text to read
                     */
                    public String read(String text) {
                        return text;
                    }

                    public String read(byte[] bytes) {
                        return new String(bytes);
                    }
                }
                """);
        Path jar = jarOf(dir, "reader-1.0", src.toString());
        try (JarOutputStream out = new JarOutputStream(
                Files.newOutputStream(dir.resolve("reader-1.0-sources.jar")))) {
            out.putNextEntry(new JarEntry("acme/Reader.java"));
            out.write(Files.readAllBytes(src));
        }

        String api = api("acme.Reader", jar);

        assertTrue(api.contains("read(byte[] arg0)"),
                "the undocumented overload names nothing it cannot know:\n" + api);
        assertTrue(!api.contains("Reads from text.") && !api.contains("read(String text)"),
                "and neither overload takes the one doc comment, since nothing tells them apart:\n" + api);
    }

    @Test
    void aJarWithNoSourcesBesideItGetsNoJavadocFromWhateverElseIsAround() throws Exception {
        Path dir = Files.createTempDirectory("wrong-version");
        Path oldSrc = dir.resolve("old/acme/Widget.java");
        Files.createDirectories(oldSrc.getParent());
        Files.writeString(oldSrc, """
                package acme;

                /** The old widget. */
                public final class Widget {
                    /**
                     * Spins it.
                     *
                     * @param turns how many turns
                     */
                    public void spin(int turns) {
                    }
                }
                """);
        Path oldJar = jarOf(dir, "widget-0.6.0", oldSrc.toString());

        // What the tool carries for the same name, from another version of the library.
        Path bundled = Files.createTempDirectory("bundled");
        Path carried = bundled.resolve("META-INF/souther-sources/acme/Widget.java");
        Files.createDirectories(carried.getParent());
        Files.writeString(carried, """
                package acme;

                /** The new widget, which is a different thing. */
                public final class Widget {
                    /**
                     * Rotates it about the axis.
                     *
                     * @param degrees how far around
                     */
                    public void spin(int degrees) {
                    }
                }
                """);

        ByteArrayOutputStream out = new ByteArrayOutputStream();
        try (java.net.URLClassLoader loader =
                     new java.net.URLClassLoader(new java.net.URL[]{bundled.toUri().toURL()}, null)) {
            assertEquals(0, JapiCommand.run(new String[]{"acme.Widget", "-cp", oldJar.toString()},
                    new PrintStream(out, true, StandardCharsets.UTF_8),
                    new PrintStream(OutputStream.nullOutputStream(), true, StandardCharsets.UTF_8), loader));
        }
        String api = out.toString(StandardCharsets.UTF_8);

        assertTrue(!api.contains("Rotates it about the axis.") && !api.contains("degrees"),
                "documentation for another copy of this name is not attached to the one on the class path:\n" + api);
        assertTrue(api.contains("spin(int arg0)"), api);
    }
}
