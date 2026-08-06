package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Search spans the specification and every shipped doc set, so the two have to be ranked against
 * each other. Ranking each side on its own and then appending one after the other means the best
 * answer is unreachable whenever the other side has enough weak matches to fill the page — and the
 * command line's own topics, being few, are the ones that disappear.
 */
class EveryDocumentIsRankedAgainstTheOthersTest {

    private List<String> search(String term) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream print = new PrintStream(out, true, StandardCharsets.UTF_8);
        assertEquals(0, DocCommand.run(new String[]{"--search", term}, print, print));
        return out.toString(StandardCharsets.UTF_8).lines()
                .filter(l -> !l.startsWith("    ") && !l.startsWith("… "))
                .toList();
    }

    @Test
    void aTopicNamedForTheTermOutranksSectionsThatMerelyMentionIt() {
        List<String> hits = search("input");

        assertTrue(hits.stream().anyMatch(l -> l.startsWith("cli/run\t")),
                "the topic written to answer this is on the page:\n" + String.join("\n", hits));
    }

    @Test
    void aTitleMatchAnywhereBeatsABodyMatchAnywhere() {
        List<String> hits = search("start");

        int titled = indexOfPrefix(hits, "cli/start-here\t");
        assertTrue(titled >= 0, "the topic titled with the term is present:\n" + String.join("\n", hits));
        assertTrue(hits.stream().limit(titled).noneMatch(l -> !l.isBlank() && bodyOnly(l)),
                "nothing that merely mentions the term is ranked above it:\n" + String.join("\n", hits));
    }

    private static boolean bodyOnly(String line) {
        String title = line.substring(line.indexOf('\t') + 1).toLowerCase();
        return !title.contains("start");
    }

    private static int indexOfPrefix(List<String> lines, String prefix) {
        for (int i = 0; i < lines.size(); i++) {
            if (lines.get(i).startsWith(prefix)) {
                return i;
            }
        }
        return -1;
    }
}
