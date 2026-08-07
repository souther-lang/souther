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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The specification's sections are asked for one by one because every heading carries an anchor its
 * author wrote. Nothing reads structure out of the prose, and that is what makes a name worth
 * publishing: it is the document's, and it stays put when the heading around it is reworded,
 * renumbered or translated.
 *
 * <p>A shipped file gets the same contract and not a weaker one. It names its own parts or it is
 * one document — a name derived here from a heading in a jar this compiler does not author would be
 * Souther's name, published as though it were the library's, and moved by an edit nobody here made.
 */
class WhatIsAddressableIsWhatTheDocSetNamedTest {

    @Test
    void aFileThatNamesItsPartsIsAskedForByThoseNames() throws Exception {
        LibraryDocs docs = shipping("""
                # A guide

                Opening words.

                <!-- souther-section: primitives -->
                ## 1. Decoding primitive values

                How a bare value is read.

                <!-- souther-section: records -->
                ## 2. Decoding records

                How an object is read.
                """);

        assertEquals(List.of("somelib/guide", "somelib/guide/primitives", "somelib/guide/records"),
                docs.topics().stream().map(LibraryDocs.Topic::name).toList());
        assertTrue(docs.read("somelib/guide/primitives").contains("How a bare value is read."));
        assertFalse(docs.read("somelib/guide/primitives").contains("How an object is read."),
                "a part stops where the next one opens");
    }

    @Test
    void aPartCarriesThePartsUnderItAndStopsAtTheNextOneBesideIt() {
        LibraryDocs docs = shipping("""
                # A guide

                <!-- souther-section: constraints -->
                ## 2. Adding constraints

                Opening words.

                <!-- souther-section: strings -->
                ### String constraints

                About strings.

                <!-- souther-section: domain -->
                ## 3. Domain primitives

                About domain primitives.
                """);

        String constraints = docs.read("somelib/guide/constraints");
        assertTrue(constraints.contains("About strings."), "asking for the larger thing asks for all of it");
        assertFalse(constraints.contains("About domain primitives."), constraints);
        assertEquals("About strings.", docs.read("somelib/guide/strings").lines()
                .filter(line -> !line.isBlank() && !line.startsWith("#") && !line.startsWith("<!--"))
                .findFirst().orElseThrow());
    }

    @Test
    void aHeadingTheSetChoseNotToNameStillClosesThePartBeforeIt() {
        LibraryDocs docs = shipping("""
                # A guide

                <!-- souther-section: named -->
                ## The one with a name

                Inside the named one.

                ## The one without

                Outside it.
                """);

        assertFalse(docs.read("somelib/guide/named").contains("Outside it."),
                "a heading is not under the part before it just because the set did not name it");
    }

    @Test
    void aFileThatNamesNoPartOfItselfIsOneDocument() {
        LibraryDocs docs = shipping("""
                # A guide

                ## Getting started

                Decode before you validate.
                """);

        assertEquals(List.of("somelib/guide"),
                docs.topics().stream().map(LibraryDocs.Topic::name).toList());
        assertNull(docs.read("somelib/guide/getting-started"),
                "a name taken from the heading would be this compiler's, and would move with an"
                        + " edit made in another repository");
        assertNull(docs.read("somelib/guide/getting started"));
    }

    @Test
    void aHeadingInsideABlockTakenAsItStandsNeitherOpensNorClosesAPart() {
        LibraryDocs docs = shipping("""
                # A guide

                <!-- souther-section: example -->
                ## Example

                ```markdown
                ## This is what the input looks like, not a section
                ```

                after the sample
                """);

        assertEquals(List.of("somelib/guide", "somelib/guide/example"),
                docs.topics().stream().map(LibraryDocs.Topic::name).toList());
        assertTrue(docs.read("somelib/guide/example").contains("after the sample"),
                "a heading shown to a reader as the words of a heading did not close the part");
    }

    @Test
    void aDeclarationWrittenInsideSuchABlockIsTheSampleAndNotAName() {
        LibraryDocs docs = shipping("""
                # A guide

                <!-- souther-section: example -->
                ## Example

                How a doc set names a part of a file:

                ```markdown
                <!-- souther-section: whatever -->
                ## Whatever
                ```
                """);

        assertEquals(List.of("somelib/guide", "somelib/guide/example"),
                docs.topics().stream().map(LibraryDocs.Topic::name).toList());
        assertNull(docs.read("somelib/guide/whatever"),
                "a sample showing how to name a part must not name one");
    }

    @Test
    void aFilesOwnPreambleIsSearchedEvenWhenTheFileNamesParts() {
        LibraryDocs docs = shipping("""
                # A guide

                Preamble prose about the command reference.

                <!-- souther-section: primitives -->
                ## Primitives

                A decoder reads a bare value.
                """);

        assertEquals(List.of("somelib/guide"),
                docs.search("command reference").stream().map(LibraryDocs.Topic::name).toList(),
                "text before the first named part is nobody else's, so it is the file's own");
    }

    @Test
    void aPartIsReadFromItsHeadingAndNotFromTheLineNamingIt() {
        LibraryDocs docs = shipping("""
                # A guide

                <!-- souther-section: primitives -->
                ## Primitives

                A decoder reads a bare value.
                """);

        assertTrue(docs.read("somelib/guide/primitives").startsWith("## Primitives"),
                "the line naming a part is that heading's, the way an anchor above a specification"
                        + " heading is: " + docs.read("somelib/guide/primitives"));
        assertTrue(docs.read("somelib/guide").contains("<!-- souther-section: primitives -->"),
                "and read from the file it is in, it is where the file says it is");
    }

    @Test
    void aNameThatOpensNothingIsRefusedWhereTheSetIsRead() {
        IllegalStateException refused = assertThrows(IllegalStateException.class, () -> shipping("""
                # A guide

                <!-- souther-section: nowhere -->
                Not a heading at all.
                """));

        assertTrue(refused.getMessage().contains("nowhere"), refused.getMessage());
    }

    @Test
    void twoPartsNamedTheSameAreRefusedTheWayTwoTopicsAre() {
        IllegalStateException refused = assertThrows(IllegalStateException.class, () -> shipping("""
                # A guide

                <!-- souther-section: same -->
                ## One

                <!-- souther-section: SAME -->
                ## Another
                """));

        assertTrue(refused.getMessage().contains("same"), refused.getMessage());
    }

    @Test
    void aSearchAnswersWithThePartWhereThereIsOneAndTheFileWhereThereIsNot() {
        LibraryDocs docs = shipping("""
                # A guide

                <!-- souther-section: primitives -->
                ## Primitives

                A decoder reads a bare value.

                <!-- souther-section: records -->
                ## Records

                A decoder reads an object.
                """);

        List<String> found = docs.search("decoder").stream().map(LibraryDocs.Topic::name).toList();

        assertEquals(List.of("somelib/guide/primitives", "somelib/guide/records"), found,
                "the smaller true answer, and the file it is in is not said again beside it");
    }

    @Test
    void whatAPartNamesInsideItselfIsCountedThereAndNotAlsoAroundIt() {
        LibraryDocs docs = shipping("""
                # A guide

                <!-- souther-section: constraints -->
                ## Constraints

                About constraints in general.

                <!-- souther-section: strings -->
                ### String constraints

                A rule written once.
                """);

        assertEquals(List.of("somelib/guide/strings"),
                docs.search("written once").stream().map(LibraryDocs.Topic::name).toList(),
                "reading `constraints` gives all of it, and searching it does not answer for what"
                        + " the part inside it already answers for");
        assertTrue(docs.read("somelib/guide/constraints").contains("A rule written once."),
                "which is a different range from the one that is read");
        assertEquals(List.of("somelib/guide/constraints"),
                docs.search("in general").stream().map(LibraryDocs.Topic::name).toList());
    }

    @Test
    void theCommandManualIsAskedForOnePartAtATime() {
        ByteArrayOutputStream listed = new ByteArrayOutputStream();
        DocCommand.run(new String[]{}, print(listed), print(listed), Caller.MCP);
        ByteArrayOutputStream part = new ByteArrayOutputStream();
        DocCommand.run(new String[]{"cli/commands/japi"}, print(part), print(part), Caller.MCP);

        assertTrue(listed.toString(StandardCharsets.UTF_8).contains("cli/commands/japi\t"),
                "a part this repository named is on the map");
        assertTrue(part.toString(StandardCharsets.UTF_8).contains("-sources.jar"),
                part.toString(StandardCharsets.UTF_8));
        assertFalse(part.toString(StandardCharsets.UTF_8).contains("souther fmt"),
                "and it is that part, not the manual it is in");
    }

    @Test
    void aLibraryThatHasNotNamedItsPartsIsStillOneDocument() {
        List<String> shipped = LibraryDocs.on(getClass().getClassLoader(), Caller.MCP).topics()
                .stream().map(LibraryDocs.Topic::name).filter(name -> name.startsWith("raoh/")).toList();

        assertEquals(List.of("raoh/tutorial", "raoh/tutorial.ja", "raoh/composition-patterns",
                        "raoh/boundary-modules", "raoh/locale-aware-messages", "raoh/comparisons"),
                shipped, "the files raoh's index promises, and nothing this compiler named for it");
    }

    private PrintStream print(ByteArrayOutputStream to) {
        return new PrintStream(to, true, StandardCharsets.UTF_8);
    }

    /** The docs of a jar shipping one file, {@code guide.md}, with this text in it. */
    private LibraryDocs shipping(String guide) {
        try {
            Path dir = Files.createTempDirectory("docset");
            Path jar = dir.resolve("somelib-1.0.jar");
            try (JarOutputStream out = new JarOutputStream(Files.newOutputStream(jar))) {
                out.putNextEntry(new JarEntry("META-INF/souther-docs/sets"));
                out.write("somelib\n".getBytes(StandardCharsets.UTF_8));
                out.putNextEntry(new JarEntry("META-INF/souther-docs/somelib/index"));
                out.write("guide.md\n".getBytes(StandardCharsets.UTF_8));
                out.putNextEntry(new JarEntry("META-INF/souther-docs/somelib/guide.md"));
                out.write(guide.getBytes(StandardCharsets.UTF_8));
            }
            return LibraryDocs.on(new URLClassLoader(new URL[]{jar.toUri().toURL()}, null), Caller.CLI);
        } catch (Exception e) {
            throw new IllegalStateException(e);
        }
    }
}
