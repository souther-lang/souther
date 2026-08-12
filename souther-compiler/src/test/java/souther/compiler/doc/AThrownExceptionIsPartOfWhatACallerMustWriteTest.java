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
 * A checked exception is not commentary on a method, it is part of how the method is called: a
 * caller who does not catch or declare it does not compile. Printing a signature without it hands
 * a reader — an agent writing against this above all — something that looks complete and is not.
 */
class AThrownExceptionIsPartOfWhatACallerMustWriteTest {

    private static Path jar;

    @BeforeAll
    static void aJarThatThrows() throws Exception {
        Path dir = Files.createTempDirectory("throws");
        Path src = dir.resolve("acme/Store.java");
        Files.createDirectories(src.getParent());
        Files.writeString(src, """
                package acme;

                import java.io.IOException;
                import java.nio.file.Path;
                import java.util.concurrent.TimeoutException;

                /** Keeps things somewhere. */
                public final class Store {

                    /** Opens a store, which may not be there. */
                    public Store(Path at) throws IOException {
                    }

                    /** Loads what is at the path. */
                    public String load(Path at) throws IOException {
                        return "";
                    }

                    /** Saves, giving up after a while. */
                    public void save(String what) throws IOException, TimeoutException {
                    }

                    /** Runs a block and lets its own failure out. */
                    public <E extends Exception> void attempt(Runnable block) throws E {
                    }

                    /** Nothing goes wrong here. */
                    public int size() {
                        return 0;
                    }
                }
                """);
        JavaCompiler javac = ToolProvider.getSystemJavaCompiler();
        Path classes = Files.createDirectories(dir.resolve("classes"));
        assertEquals(0, javac.run(null, OutputStream.nullOutputStream(), OutputStream.nullOutputStream(),
                "-d", classes.toString(), "-parameters", src.toString()));
        jar = dir.resolve("store-1.0.jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            try (Stream<Path> files = Files.walk(classes)) {
                for (Path f : files.filter(Files::isRegularFile).toList()) {
                    out.putNextEntry(new JarEntry(classes.relativize(f).toString()));
                    out.write(Files.readAllBytes(f));
                }
            }
        }
    }

    private static String api() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        assertEquals(0, JapiCommand.run(new String[]{"acme.Store", "-cp", jar.toString()},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(OutputStream.nullOutputStream(), true, StandardCharsets.UTF_8)));
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void aMethodSaysWhatItThrows() {
        assertTrue(api().contains("load(java.nio.file.Path at) throws java.io.IOException"), api());
    }

    @Test
    void severalThrownTypesAreAllNamed() {
        String api = api();

        assertTrue(api.contains("save(String what) throws java.io.IOException,"
                + " java.util.concurrent.TimeoutException"), api);
    }

    @Test
    void aConstructorSaysWhatItThrows() {
        assertTrue(api().contains("Store(java.nio.file.Path at) throws java.io.IOException"), api());
    }

    @Test
    void aThrownTypeVariableIsNamedAsItWasWritten() {
        assertTrue(api().contains("attempt(Runnable block) throws E"), api());
    }

    @Test
    void aMethodThatThrowsNothingCheckedSaysNothing() {
        assertTrue(api().lines().filter(l -> l.contains("size(")).noneMatch(l -> l.contains("throws")),
                api());
    }
}
