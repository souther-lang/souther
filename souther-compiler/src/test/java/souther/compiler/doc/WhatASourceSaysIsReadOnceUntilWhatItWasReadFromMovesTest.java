package souther.compiler.doc;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import javax.tools.ToolProvider;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.OutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.FileTime;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Reading a source for its documentation runs the compiler's front end, and a server asks the same
 * class again — for another member, or for the next part of an answer — while nothing it was read
 * from has moved. What is held to is how many times the front end is run, counted at the reader a
 * session's memo is handed, because that is what a regression here would look like whatever the
 * machine: the memo bypassed, and every call paying for javac again.
 *
 * <p>What it was read from moving is the other half. A memo that answered after the source or the
 * class path changed would hand back documentation for a library that is no longer there.
 */
class WhatASourceSaysIsReadOnceUntilWhatItWasReadFromMovesTest {

    private Path root;
    private Path jar;
    private Path sources;
    private final AtomicInteger read = new AtomicInteger();
    private SourceDocs memo;

    @BeforeEach
    void aJarAndItsSources() throws IOException {
        root = Files.createTempDirectory("source-docs");
        Path src = Files.createDirectories(root.resolve("src/acme")).resolve("Widget.java");
        Files.writeString(src, widget("Turns once."));
        Path classes = Files.createDirectories(root.resolve("classes"));
        assertEquals(0, ToolProvider.getSystemJavaCompiler().run(null, OutputStream.nullOutputStream(),
                OutputStream.nullOutputStream(), "-proc:none", "-d", classes.toString(), src.toString()));
        jar = root.resolve("widget-1.0.jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            out.putNextEntry(new JarEntry("acme/Widget.class"));
            out.write(Files.readAllBytes(classes.resolve("acme/Widget.class")));
        }
        sources = root.resolve("widget-1.0-sources.jar");
        writeSources("Turns once.");
        memo = new SourceDocs((source, binaryName, classPath, confined) -> {
            read.incrementAndGet();
            return SourceDoc.of(source, binaryName, classPath, confined);
        });
    }

    private static String widget(String doc) {
        return """
                package acme;

                public final class Widget {
                    /** %s */
                    public void turn(int times) {}
                }
                """.formatted(doc);
    }

    private void writeSources(String doc) throws IOException {
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(sources))) {
            out.putNextEntry(new JarEntry("acme/Widget.java"));
            out.write(widget(doc).getBytes(StandardCharsets.UTF_8));
        }
    }

    private String asked(String classPath) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = JapiCommand.runConfined(new String[]{"acme.Widget", "-cp", classPath},
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8), root, memo);
        assertEquals(0, code, err.toString(StandardCharsets.UTF_8));
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void theSameClassAskedAgainIsNotReadAgain() {
        String first = asked(jar.toString());
        String second = asked(jar.toString());

        assertTrue(first.contains("Turns once."), "the source was read at all: " + first);
        assertEquals(first, second, "and the answer is the same answer");
        assertEquals(1, read.get(), "the front end ran once for two calls about one class");
    }

    @Test
    void aSourceThatChangedIsReadAgain() throws IOException {
        asked(jar.toString());
        writeSources("Turns twice.");

        String after = asked(jar.toString());

        assertTrue(after.contains("Turns twice."), "the documentation is the source's as it is now: " + after);
        assertEquals(2, read.get());
    }

    @Test
    void aClassPathEntryThatMovedIsReadAgainThoughTheSourceDidNot() throws IOException {
        asked(jar.toString());
        // The types a source names are resolved against the class path, so an entry that changed
        // can change what the source says even when its text did not.
        Files.setLastModifiedTime(jar, FileTime.fromMillis(Files.getLastModifiedTime(jar).toMillis() + 60_000));

        asked(jar.toString());

        assertEquals(2, read.get());
    }

    @Test
    void aClassPathWithADirectoryOnItIsReadEveryTime() throws IOException {
        // A directory has no stamp that says whether anything below it moved.
        String withADirectory = jar + File.pathSeparator + Files.createDirectories(root.resolve("more"));

        asked(withADirectory);
        asked(withADirectory);

        assertEquals(2, read.get());
    }
}
