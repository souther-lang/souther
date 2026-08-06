package souther.compiler.doc;

import org.junit.jupiter.api.BeforeAll;
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
 * Parameter names recovered from javadoc are only worth having if they belong to the method they
 * are printed against. Overloading is ordinary in Java, and a name keyed by method name alone hands
 * every overload the first one's prose and the first one's argument order — which reads as fact and
 * is not.
 */
class AnOverloadDoesNotInheritItsNamesakesDocumentationTest {

    private static Path jar;

    @BeforeAll
    static void aJarOfOverloads() throws Exception {
        Path dir = Files.createTempDirectory("overloads");
        Path src = dir.resolve("acme/Codec.java");
        Files.createDirectories(src.getParent());
        Files.writeString(src, """
                package acme;

                import java.nio.charset.Charset;

                /** Turns things into other things. */
                public final class Codec {

                    /**
                     * Decodes text that is already a string.
                     *
                     * @param text the text to decode
                     */
                    public String decode(String text) {
                        return text;
                    }

                    /**
                     * Decodes bytes under a character set.
                     *
                     * @param bytes the encoded bytes
                     * @param charset the character set they are in
                     */
                    public String decode(byte[] bytes, Charset charset) {
                        return new String(bytes, charset);
                    }

                    /**
                     * Encodes with a separator.
                     *
                     * @param first the first part
                     * @param second the second part
                     */
                    public String encode(String first, String second) {
                        return first + second;
                    }

                    /**
                     * Encodes with a repeat count.
                     *
                     * @param part the part to repeat
                     * @param times how many times
                     */
                    public String encode(String part, int times) {
                        return part.repeat(times);
                    }
                }
                """);
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        Path classes = dir.resolve("classes");
        Files.createDirectories(classes);
        assertEquals(0, javac.run(null, OutputStream.nullOutputStream(), OutputStream.nullOutputStream(),
                "-d", classes.toString(), src.toString()));

        jar = dir.resolve("codec-1.0.jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            try (Stream<Path> files = Files.walk(classes)) {
                for (Path f : files.filter(Files::isRegularFile).toList()) {
                    out.putNextEntry(new JarEntry(classes.relativize(f).toString()));
                    out.write(Files.readAllBytes(f));
                }
            }
        }
        try (JarOutputStream out = new JarOutputStream(
                Files.newOutputStream(dir.resolve("codec-1.0-sources.jar")))) {
            out.putNextEntry(new JarEntry("acme/Codec.java"));
            out.write(Files.readAllBytes(src));
        }
    }

    private String api() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        assertEquals(0, JapiCommand.run(new String[]{"acme.Codec", "-cp", jar.toString()},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(OutputStream.nullOutputStream(), true, StandardCharsets.UTF_8)));
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void eachArityKeepsItsOwnParameterNames() {
        String api = api();

        assertTrue(api.contains("decode(String text)"), api);
        assertTrue(api.contains("decode(byte[] bytes, java.nio.charset.Charset charset)"), api);
    }

    @Test
    void eachArityKeepsItsOwnProse() {
        String api = api();

        int oneArgDoc = api.indexOf("Decodes text that is already a string.");
        int oneArg = api.indexOf("decode(String text)");
        int twoArgDoc = api.indexOf("Decodes bytes under a character set.");
        int twoArg = api.indexOf("decode(byte[] bytes,");

        assertTrue(oneArgDoc >= 0 && twoArgDoc >= 0, "both sentences are printed:\n" + api);
        assertTrue(oneArgDoc < oneArg && oneArg < twoArgDoc && twoArgDoc < twoArg,
                "each sentence sits above the overload it was written for:\n" + api);
    }

    @Test
    void twoOverloadsOfTheSameCountSayNothingRatherThanSayTheWrongThing() {
        String api = api();

        assertTrue(api.contains("encode(String arg0, String arg1)"), api);
        assertTrue(api.contains("encode(String arg0, int arg1)"), api);
        assertTrue(!api.contains("Encodes with a separator.") && !api.contains("Encodes with a repeat count."),
                "neither doc is attached, because nothing here distinguishes the two:\n" + api);
    }
}
