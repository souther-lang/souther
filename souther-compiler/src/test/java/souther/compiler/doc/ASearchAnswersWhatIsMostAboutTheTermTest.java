package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A word common enough to appear in most of the specification is useless as a flat list — over
 * half the document comes back and nothing is chosen. Search ranks instead: a section titled with
 * the term comes first, then the sections that dwell on it, and the tail is cut off with a count
 * of what was left.
 */
class ASearchAnswersWhatIsMostAboutTheTermTest {

    private final SpecDocument spec = SpecDocument.of("""
            = A Specification

            [#passing]
            == Passing mention

            A guard appears here once.

            [#dwelling]
            == Dwelling on it

            A guard, then another guard, and a third guard for good measure.

            [#guard]
            == Guard

            The section named for it, which mentions it nowhere else.
            """);

    @Test
    void aSectionTitledWithTheTermComesFirstHoweverLittleItSaysIt() {
        List<SpecDocument.Hit> hits = spec.rank("guard");

        assertEquals("guard", hits.getFirst().section().anchor());
    }

    @Test
    void theSectionsThatDwellOnTheTermOutrankThoseThatMentionItOnce() {
        List<SpecDocument.Hit> hits = spec.rank("guard");

        assertEquals(List.of("guard", "dwelling", "passing"),
                hits.stream().map(h -> h.section().anchor()).toList());
    }

    @Test
    void aHitCarriesHowOftenTheSectionSaysTheTerm() {
        List<SpecDocument.Hit> hits = spec.rank("guard");

        assertEquals(3, hits.stream().filter(h -> h.section().anchor().equals("dwelling"))
                .findFirst().orElseThrow().occurrences());
    }

    @Test
    void aCommonWordDoesNotAnswerWithHalfTheSpecification() {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream print = new PrintStream(out, true, StandardCharsets.UTF_8);

        assertEquals(0, DocCommand.run(new String[]{"--search", "type"}, print, print));

        List<String> lines = out.toString(StandardCharsets.UTF_8).lines().toList();
        long hits = lines.stream().filter(l -> !l.startsWith("    ") && !l.startsWith("… ")).count();
        assertTrue(hits <= 20, "the answer is cut to a readable length, got " + hits + " hits");
        assertTrue(lines.getLast().startsWith("… "),
                "what was cut off is counted rather than silently dropped: " + lines.getLast());
    }

    @Test
    void theLimitIsLiftedOnAsking() {
        long capped = searchLineCount("--search", "type");
        long all = searchLineCount("--search", "type", "--limit", "0");

        assertTrue(all > capped, "`--limit 0` answers with everything: " + all + " vs " + capped);
    }

    private static long searchLineCount(String... args) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream print = new PrintStream(out, true, StandardCharsets.UTF_8);
        assertEquals(0, DocCommand.run(args, print, print));
        return out.toString(StandardCharsets.UTF_8).lines()
                .filter(l -> !l.startsWith("    ") && !l.startsWith("… "))
                .count();
    }
}
