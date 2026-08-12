package souther.compiler.fmt;

import souther.cli.Main;
import org.junit.jupiter.api.Test;

import souther.compiler.fmt.Deviations;

import java.io.IOException;
import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The rules `fmt --check` can name are the rules the documentation defines.
 *
 * <p>A line of that report carries no diagnostic code, so there is nothing on it to look up: a
 * reader who does not recognise the words has only the section that fixes them. That makes the two
 * sets one contract rather than two lists, and a rule added to the report without a definition is
 * a word the tool says to people who cannot find out what it means.
 *
 * <p>Held both ways. A rule the report can name and the section does not define is the failure this
 * was written for; a rule the section defines and the report cannot name is a definition of
 * something that no longer happens, which sends a reader looking for a line they will never see.
 */
class EveryWordTheFormatReportUsesIsWrittenDownTest {

    private static final String DOC = "/META-INF/souther-docs/cli/commands.md";
    private static final String SECTION = "<!-- souther-section: fmt-report-vocabulary -->";

    private static String doc() throws IOException {
        try (InputStream in = Main.class.getResourceAsStream(DOC)) {
            assertTrue(in != null, "the shipped documentation is not on the classpath: " + DOC);
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        }
    }

    /** The vocabulary section, up to whatever section follows it. */
    private static String section(String text) {
        int from = text.indexOf(SECTION);
        assertTrue(from >= 0, "the vocabulary section is gone: " + SECTION);
        int to = text.indexOf("<!-- souther-section:", from + SECTION.length());
        return to < 0 ? text.substring(from) : text.substring(from, to);
    }

    /**
     * What the section defines: the rule each list item opens with.
     *
     * <p>An item is one rule, written as the report writes it and followed by what it means. A
     * continuation line belongs to the item above it, so the two are joined before the rule is
     * read off — otherwise a rule long enough to wrap would be read as a shorter one.
     */
    private static Set<String> defined(String section) {
        List<String> items = new ArrayList<>();
        for (String line : section.split("\n", -1)) {
            if (line.startsWith("- ")) {
                items.add(line.substring(2).strip());
            } else if (!items.isEmpty() && line.startsWith("  ") && !line.isBlank()) {
                items.set(items.size() - 1, items.getLast() + " " + line.strip());
            }
        }
        Set<String> out = new LinkedHashSet<>();
        for (String item : items) {
            int em = item.indexOf(" — ");
            out.add((em < 0 ? item : item.substring(0, em)).strip().replaceAll("\\.$", ""));
        }
        return out;
    }

    @Test
    void everyRuleTheReportCanNameIsDefined() throws IOException {
        Set<String> defined = defined(section(doc()));

        List<String> missing = new ArrayList<>();
        for (String rule : Deviations.vocabulary()) {
            if (!defined.contains(rule)) {
                missing.add(rule);
            }
        }

        assertEquals(List.of(), missing,
                "these rules are printed and not written down anywhere: " + missing);
    }

    @Test
    void andEveryRuleDefinedIsOneTheReportCanName() throws IOException {
        Set<String> emitted = Deviations.vocabulary();

        List<String> stale = new ArrayList<>();
        for (String rule : defined(section(doc()))) {
            if (!emitted.contains(rule)) {
                stale.add(rule);
            }
        }

        assertEquals(List.of(), stale,
                "these are defined and nothing can print them: " + stale);
    }

    /** And the section was found rather than an empty stretch of the file being read as one. */
    @Test
    void andTheSectionIsTheOneWithTheRulesInIt() throws IOException {
        assertEquals(Deviations.vocabulary().size(), defined(section(doc())).size(),
                "the section defines one rule per rule there is");
    }
}
