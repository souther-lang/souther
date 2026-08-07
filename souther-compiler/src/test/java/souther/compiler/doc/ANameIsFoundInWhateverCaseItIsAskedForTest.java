package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name reaches the lookup in whatever case its writer used. The specification anchors a
 * diagnostic {@code e2010} and the compiler prints that diagnostic {@code E2010}, so the form a
 * reader copies out of an error is not the form the document registers — and answering `no section`
 * to it tells the reader about the anchors' spelling, which is nothing they asked about.
 *
 * <p>Only the lookup key is folded. A shipped topic's name is also the path its text is read from,
 * and the class path resolves that by the spelling on the file, so folding the name itself would
 * answer for a topic and then fail to read it.
 */
class ANameIsFoundInWhateverCaseItIsAskedForTest {

    private record Answer(int code, String out, String err) {}

    private static Answer run(ClassLoader loader, String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = DocCommand.run(args,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8), loader);
        return new Answer(code, out.toString(StandardCharsets.UTF_8), err.toString(StandardCharsets.UTF_8));
    }

    @Test
    void aSectionAnsweredForItsAnchorIsAnsweredForTheCaseTheCompilerPrints() {
        SpecDocument spec = SpecDocument.bundled();

        SpecDocument.Section written = spec.section("e2010");

        assertNotNull(written, "the specification anchors this one");
        assertSame(written, spec.section("E2010"), "the case an error is printed in");

        SpecDocument.Section named = spec.section("newtype");

        assertNotNull(named, "a section named by a word rather than by a code");
        assertSame(named, spec.section("NewType"), "and any other case of it");
    }

    @Test
    void theDocCommandReadsASectionAskedForInTheCaseTheCompilerPrints() {
        Answer answer = run(DocCommand.class.getClassLoader(), "E2010");

        assertEquals(0, answer.code(), answer.err());
        assertTrue(answer.out().contains("[#e2010]"),
                "the section is printed under the anchor the specification writes: " + answer.out());
    }

    @Test
    void aNearMissIsSuggestedForTheCaseTheCompilerPrintsToo() {
        Answer answer = run(DocCommand.class.getClassLoader(), "E1001");

        assertEquals(2, answer.code());
        assertTrue(answer.err().contains("did you mean: e1001-removed"),
                "the suggestion goes through the same fold as the lookup: " + answer.err());
    }

    @Test
    void aShippedTopicKeepsItsSpellingAndIsStillFoundByAnyCase() throws Exception {
        try (URLClassLoader loader = jarOf("MixedCase", List.of("Guide.md"))) {
            LibraryDocs docs = LibraryDocs.on(loader);

            assertEquals(List.of("MixedCase/Guide"),
                    docs.topics().stream().map(LibraryDocs.Topic::name).toList(),
                    "the name is the jar's, since it is also where the text is");
            assertTrue(docs.read("mixedcase/guide").contains("Text of Guide."),
                    "and it is read through a name folded to any case");
            assertTrue(docs.read("MixedCase/Guide").contains("Text of Guide."));

            Answer answer = run(loader, "MIXEDCASE/GUIDE");
            assertEquals(0, answer.code(), answer.err());
            assertTrue(answer.out().contains("Text of Guide."), answer.out());
        }
    }

    @Test
    void twoNamesThatFoldTogetherAreRefusedRatherThanOneWinningSilently() {
        String adoc = """
                = A specification

                [#Alpha]
                == Written one way

                Something.

                [#alpha]
                == Written the other

                Something else.
                """;

        IllegalStateException refused = assertThrows(IllegalStateException.class,
                () -> SpecDocument.of(adoc));

        assertTrue(refused.getMessage().contains("Alpha") && refused.getMessage().contains("alpha"),
                "the refusal names both of them: " + refused.getMessage());
    }

    @Test
    void twoShippedTopicsThatFoldTogetherAreRefusedTheSameWay() throws Exception {
        try (URLClassLoader loader = jarOf("somelib", List.of("Guide.md", "guide.md"))) {
            IllegalStateException refused =
                    assertThrows(IllegalStateException.class, () -> LibraryDocs.on(loader));

            assertTrue(refused.getMessage().contains("somelib/Guide")
                            && refused.getMessage().contains("somelib/guide"),
                    "the refusal names both of them: " + refused.getMessage());
        }
    }

    /** A jar shipping one doc set, whose topics are the given files, each holding its own name. */
    private static URLClassLoader jarOf(String set, List<String> files) throws Exception {
        Path jar = Files.createTempDirectory("docset").resolve(set + "-1.0.jar");
        try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
            out.putNextEntry(new JarEntry("META-INF/souther-docs/sets"));
            out.write((set + "\n").getBytes(StandardCharsets.UTF_8));
            out.putNextEntry(new JarEntry("META-INF/souther-docs/" + set + "/index"));
            out.write((String.join("\n", files) + "\n").getBytes(StandardCharsets.UTF_8));
            for (String file : files) {
                String topic = file.replaceFirst("\\.md$", "");
                out.putNextEntry(new JarEntry("META-INF/souther-docs/" + set + "/" + file));
                out.write(("# " + topic + "\n\nText of " + topic + ".\n").getBytes(StandardCharsets.UTF_8));
            }
        }
        return new URLClassLoader(new URL[]{jar.toUri().toURL()}, null);
    }
}
