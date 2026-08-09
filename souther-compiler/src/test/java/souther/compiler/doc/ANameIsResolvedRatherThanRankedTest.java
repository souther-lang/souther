package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A name is answered by resolving it, and a name is what a reader arriving from a diagnostic has:
 * {@code E1313} cites {@code an-optional-does-not-stand-in-a-boundary}, and a reader who reaches for
 * a search with it in hand is holding an identifier rather than a description.
 *
 * <p>So the name space the read path answers over is the search's first question, and it either
 * answers or it does not. Scoring a name against prose instead would leave which section an
 * identifier resolves to decided by how often the specification happens to say its words, and a name
 * whose section never writes it out — which every heading anchor is, the anchor line belonging to no
 * section's body — would resolve to the sections that cite it and never to the one it names.
 */
class ANameIsResolvedRatherThanRankedTest {

    private final SpecDocument spec = SpecDocument.bundled();
    private final LibraryDocs shipped = LibraryDocs.on(getClass().getClassLoader(), Caller.CLI);

    /** The same name with its segments written as the words they are, which is how a reader says it. */
    private static String asWords(String name) {
        return name.replaceAll("[^A-Za-z0-9]+", " ").strip();
    }

    private record Answer(int code, String out, String err) {}

    private Answer run(String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        int code = DocCommand.run(args,
                new PrintStream(out, true, StandardCharsets.UTF_8),
                new PrintStream(err, true, StandardCharsets.UTF_8));
        return new Answer(code, out.toString(StandardCharsets.UTF_8), err.toString(StandardCharsets.UTF_8));
    }

    @Test
    void everyNameTheReadPathResolvesTheSearchResolvesToo() {
        List<String> unresolved = new ArrayList<>();
        for (String name : spec.names()) {
            SpecDocument.Section resolved = spec.named(name);
            if (resolved == null || !resolved.anchor().equals(spec.section(name).anchor())) {
                unresolved.add(name + " -> " + (resolved == null ? "nothing" : resolved.anchor()));
            }
        }
        for (LibraryDocs.Topic topic : shipped.topics()) {
            LibraryDocs.Topic resolved = shipped.named(topic.name());
            if (resolved == null || !resolved.name().equals(topic.name())) {
                unresolved.add(topic.name() + " -> " + (resolved == null ? "nothing" : resolved.name()));
            }
        }

        assertEquals(List.of(), unresolved,
                "what one tool answers for by name is what the other one looks for first");
    }

    @Test
    void andResolvesItWrittenAsTheWordsItIsMadeOf() {
        List<String> unresolved = new ArrayList<>();
        for (String name : spec.names()) {
            SpecDocument.Section resolved = spec.named(asWords(name));
            if (resolved == null || !resolved.anchor().equals(spec.section(name).anchor())) {
                unresolved.add(asWords(name) + " -> " + (resolved == null ? "nothing" : resolved.anchor()));
            }
        }
        for (LibraryDocs.Topic topic : shipped.topics()) {
            LibraryDocs.Topic resolved = shipped.named(asWords(topic.name()));
            if (resolved == null || !resolved.name().equals(topic.name())) {
                unresolved.add(asWords(topic.name()) + " -> "
                        + (resolved == null ? "nothing" : resolved.name()));
            }
        }

        assertEquals(List.of(), unresolved,
                "a reader types the name a document cites, and a document cites it in prose as its"
                        + " words: the hyphens are the anchor's spelling and not part of what it names");
    }

    @Test
    void aSearchForANameAnswersWithThatSectionAndNothingBeside() {
        Answer searched = run("--search", "an optional does not stand in a boundary");
        Answer read = run("an-optional-does-not-stand-in-a-boundary");

        assertEquals(read.out(), searched.out(),
                "the search answers with the section, not with a page of sections that share a word");
        assertTrue(searched.err().contains("is a name written in `external-representation`"),
                "and says the term was taken as a name, and which section holds the rule it names: "
                        + searched.err());
    }

    @Test
    void aDiagnosticCodeIsANameAndNotATermToBeScored() {
        Answer searched = run("--search", "E1004");
        Answer read = run("E1004");

        assertEquals(read.out(), searched.out(),
                "the code the compiler printed is what a reader searches with first");
        assertTrue(searched.out().contains("[#e1004]"), "and it resolves: " + searched.out());
        assertTrue(searched.err().contains("is a name"),
                "and the reader is told why one section came back rather than a list: " + searched.err());
    }

    @Test
    void aQueryWhoseWordsAreNowhereIsToldThatAndNotToldItTwice() {
        Answer searched = run("--search", "borrowck zzyzx");

        assertTrue(searched.err().contains("nothing says `borrowck zzyzx`"),
                "the term drew a blank and that is the whole of it: " + searched.err());
        assertTrue(!searched.err().contains("ranking"),
                "a ranking that ranked nothing is not something that happened: " + searched.err());
        assertEquals("", searched.out());
    }

    @Test
    void aNameAnswersWithTheSectionItNamesAndNotTheSectionsThatCiteIt() {
        Answer searched = run("--search", "mapping-principle");

        assertTrue(searched.out().contains("[#mapping-principle]"),
                "`mapping-principle` is written in prose only where another section cites it, and"
                        + " the section it names is the answer: " + searched.out());
    }

    @Test
    void aNameOutranksASectionWhoseTitleReadsTheSameWay() {
        Answer searched = run("--search", "behavior");

        assertTrue(searched.out().contains("[#behavior]"),
                "`jvm-behavior` is titled `behavior`, and a title is not an identity: " + searched.out());
    }

    @Test
    void aTermThatNamesNothingIsSearchedForAsBefore() {
        Answer searched = run("--search", "type");

        assertEquals(0, searched.code());
        assertTrue(searched.out().lines().anyMatch(l -> l.matches("\\S+\t.*")),
                "a term that is nobody's name is still ranked across the sections that say it:\n"
                        + searched.out());
    }
}
