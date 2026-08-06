package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A list of section names is a filtered table of contents, not a search: the reader cannot tell a
 * section that is about the term from one that says it in passing without opening each. Every hit
 * carries the line it matched on, so the choice is made from the answer rather than from the title.
 */
class ASearchHitShowsWhyItMatchedTest {

    private final SpecDocument spec = SpecDocument.of("""
            = A Specification

            [#guard]
            == Guard

            A guard departs by the value written after `else`.

            [#elsewhere]
            == Something else

            Most of this section is about other matters entirely. A guard is mentioned here once.
            """);

    @Test
    void aHitCarriesTheSentenceTheTermWasFoundIn() {
        List<SpecDocument.Hit> hits = spec.rank("departs");

        assertEquals(1, hits.size());
        assertTrue(hits.getFirst().snippet().contains("departs by the value written after"),
                "the matched line comes back with the hit: " + hits.getFirst().snippet());
    }

    @Test
    void aSectionMatchedOnlyByItsTitleStillOffersItsOpeningLine() {
        List<SpecDocument.Hit> hits = spec.rank("Guard");

        SpecDocument.Hit titled = hits.getFirst();
        assertTrue(titled.titled());
        assertTrue(!titled.snippet().isBlank(), "a title-only hit is not left blank");
    }

    @Test
    void theCommandPrintsTheSnippetUnderneathItsHit() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream print = new PrintStream(out, true, StandardCharsets.UTF_8);

        assertEquals(0, DocCommand.run(new String[]{"--search", "newtype"}, print, print));

        List<String> lines = out.toString(StandardCharsets.UTF_8).lines().toList();
        assertTrue(lines.getFirst().matches("\\S+\t.*"), "a hit is still one tab-separated line: " + lines.getFirst());
        assertTrue(lines.get(1).startsWith("    "),
                "and the line it matched on sits indented under it: " + lines.get(1));
    }

    @Test
    void aSnippetIsOneLineHoweverLongTheParagraphIs() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream print = new PrintStream(out, true, StandardCharsets.UTF_8);

        DocCommand.run(new String[]{"--search", "invariant"}, print, print);

        assertTrue(out.toString(StandardCharsets.UTF_8).lines()
                        .filter(l -> l.startsWith("    "))
                        .allMatch(l -> l.length() <= 140),
                "no snippet runs past a readable width:\n" + out);
    }
}
