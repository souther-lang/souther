package souther.compiler.doc;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A dependency ships its own documentation inside its jar, under
 * {@code META-INF/souther-docs/<set>/}: a {@code sets} registry names the set, an {@code index}
 * lists its topics. `souther doc` then answers {@code <set>/<topic>` from whatever is on its own
 * class path — raoh's docs arrive by the CLI bundling the raoh jar, with no copy kept anywhere.
 */
class ALibraryShipsItsOwnDocsTest {

    private static URLClassLoader loader;

    @BeforeAll
    static void aJarCarryingDocs() throws Exception {
        Path dir = Files.createTempDirectory("docset");
        Path jar = dir.resolve("somelib-1.0.jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            out.putNextEntry(new JarEntry("META-INF/souther-docs/sets"));
            out.write("somelib\n".getBytes(StandardCharsets.UTF_8));
            out.putNextEntry(new JarEntry("META-INF/souther-docs/somelib/index"));
            out.write("tutorial.md\npatterns.md\n".getBytes(StandardCharsets.UTF_8));
            out.putNextEntry(new JarEntry("META-INF/souther-docs/somelib/tutorial.md"));
            out.write("# Getting started\n\nDecode before you validate.\n".getBytes(StandardCharsets.UTF_8));
            out.putNextEntry(new JarEntry("META-INF/souther-docs/somelib/patterns.md"));
            out.write("# Composition patterns\n\nCompose decoders, not booleans.\n".getBytes(StandardCharsets.UTF_8));
        }
        loader = new URLClassLoader(new java.net.URL[]{jar.toUri().toURL()}, null);
    }

    @Test
    void everyTopicOfEveryShippedSetIsListedWithItsTitle() {
        LibraryDocs docs = LibraryDocs.on(loader);

        List<LibraryDocs.Topic> topics = docs.topics();

        assertEquals(List.of("somelib/tutorial", "somelib/patterns"),
                topics.stream().map(LibraryDocs.Topic::name).toList());
        assertEquals("Getting started", topics.getFirst().title());
    }

    @Test
    void aTopicIsReadBackByItsName() {
        LibraryDocs docs = LibraryDocs.on(loader);

        assertTrue(docs.read("somelib/tutorial").contains("Decode before you validate."));
    }

    @Test
    void searchFindsTopicsByWhatTheirTextSays() {
        LibraryDocs docs = LibraryDocs.on(loader);

        List<LibraryDocs.Topic> hits = docs.search("booleans");

        assertEquals(List.of("somelib/patterns"), hits.stream().map(LibraryDocs.Topic::name).toList());
    }

    @Test
    void theDocCommandListsReadsAndSearchesTheShippedSets() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream print = new PrintStream(out, true, StandardCharsets.UTF_8);

        assertEquals(0, DocCommand.run(new String[]{}, print, print, loader));
        assertTrue(out.toString(StandardCharsets.UTF_8).lines()
                        .anyMatch(l -> l.startsWith("somelib/tutorial\t")),
                "the listing carries the shipped set after the spec sections:\n" + out);

        out.reset();
        assertEquals(0, DocCommand.run(new String[]{"somelib/patterns"}, print, print, loader));
        assertTrue(out.toString(StandardCharsets.UTF_8).contains("Compose decoders, not booleans."));

        out.reset();
        assertEquals(0, DocCommand.run(new String[]{"--search", "validate"}, print, print, loader));
        assertTrue(out.toString(StandardCharsets.UTF_8).lines()
                .anyMatch(l -> l.startsWith("somelib/tutorial\t")), out.toString(StandardCharsets.UTF_8));
    }
}
