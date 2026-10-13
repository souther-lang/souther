package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.InputStream;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An option this compiler takes is written where a caller looks it up.
 *
 * <p>Three statements of the command line already agree with each other, and all three are in
 * {@code Main}: the table of which commands take what, the usage text, and each parser's own cases. A
 * test holds them together. The document {@code souther doc} answers from is a fourth, and it was
 * outside that agreement — which is how {@code --warnings} came to be in the usage text, in the table,
 * in a parser and in a test, and in no document at all. From a caller's side that is the same as not
 * having it.
 *
 * <p>Asked per section rather than of the whole file. An option written under some other command's
 * heading is one a reader of the command they are using does not find.
 */
class AnOptionIsDocumentedUnderEveryCommandThatTakesItTest {

    private static final String RESOURCE = "META-INF/souther-docs/cli/commands.md";

    /** Where the options every command shares are written, instead of under each of them. */
    private static final String SHARED = "shared-options";

    private static final Pattern SECTION =
            Pattern.compile("<!--\\s*souther-section:\\s*(\\S+)\\s*-->");

    @Test
    void everyOptionIsWrittenUnderEachCommandThatTakesIt() throws Exception {
        Map<String, String> sections = sections();
        List<String> missing = new ArrayList<>();

        for (String option : Main.knownOptions()) {
            if (mentions(sections.get(SHARED), option)) {
                continue;   // written once, for the commands that all take it
            }
            for (String owner : Main.optionOwners(option).split("/")) {
                String section = sections.get(owner);
                assertNotNull(section, "no `" + owner + "` section in " + RESOURCE);
                if (!mentions(section, option)) {
                    missing.add(option + " under " + owner);
                }
            }
        }

        assertTrue(missing.isEmpty(),
                "options this compiler takes and " + RESOURCE + " does not write: " + missing);
    }

    /**
     * And the other way round: what a usage line writes is an option its command takes, with the
     * value words the command reads.
     *
     * <p>A usage line is a promise a reader acts on, so one naming an option the parser refuses — or
     * a value word it refuses — sends them to a refusal. Asked of the usage lines rather than of the
     * prose, which may name an option to say it is not taken.
     *
     * <p>{@code --target} is read before any option, by the command line that hands everything
     * after it to a backend, so it and what follows it are not this table's.
     */
    @Test
    void everyOptionAUsageLineWritesIsOneItsCommandTakes() throws Exception {
        Map<String, CliOption> bySpelling = new LinkedHashMap<>();
        for (CliOption option : CliOption.values()) {
            option.spellings().forEach(spelling -> bySpelling.put(spelling, option));
        }
        List<String> refused = new ArrayList<>();
        List<String> read = new ArrayList<>();
        for (String usage : usageLines(sections())) {
            String command = usage.split("\\s+", 3)[1];
            String written = usage.contains(" --target ")
                    ? usage.substring(0, usage.indexOf(" --target ")) : usage;
            Matcher option = USAGE_OPTION.matcher(written);
            while (option.find()) {
                String spelling = option.group(1);
                read.add(command + " " + spelling);
                CliOption taken = bySpelling.get(spelling);
                if (taken == null || !taken.ownedBy(command)) {
                    refused.add(spelling + " under " + command);
                    continue;
                }
                String choice = option.group(2);
                if (choice != null && !choice.equals(taken.valueSpelling())) {
                    refused.add(spelling + " " + choice + " under " + command + ", which takes "
                            + taken.valueSpelling());
                }
            }
        }

        assertTrue(read.contains("compile --adequacy"), () -> "usage lines read: " + read);
        assertTrue(refused.isEmpty(),
                RESOURCE + " writes in a usage line what its command does not take: " + refused);
    }

    /** An option in a usage line, and the value words written after it where it writes a choice. */
    private static final Pattern USAGE_OPTION = Pattern.compile(
            "(?<![\\w<-])(--?[A-Za-z][\\w-]*)(?: ([a-z][\\w-]*(?:\\|[a-z][\\w-]*)+))?");

    /**
     * Each usage statement in the document: a line in a fenced block that starts with
     * {@code souther <command>}, joined with the indented lines that continue it.
     */
    private static List<String> usageLines(Map<String, String> sections) {
        List<String> usages = new ArrayList<>();
        for (String section : sections.values()) {
            boolean fenced = false;
            StringBuilder current = null;
            for (String line : section.lines().toList()) {
                if (line.startsWith("```")) {
                    fenced = !fenced;
                }
                boolean continues = current != null && fenced && !line.isBlank()
                        && Character.isWhitespace(line.charAt(0));
                if (continues) {
                    current.append(' ').append(line.strip());
                    continue;
                }
                if (current != null) {
                    usages.add(current.toString());
                    current = null;
                }
                if (fenced && line.startsWith("souther ")) {
                    current = new StringBuilder(line.strip());
                }
            }
            if (current != null) {
                usages.add(current.toString());
            }
        }
        return usages;
    }

    /**
     * Whether the section writes this option, and not one it is the beginning of.
     *
     * <p>{@code -w} is in {@code --write} and {@code --color} is not {@code --colour}; a plain search
     * would call the first documented by the second and would be right by accident.
     */
    private static boolean mentions(String section, String option) {
        if (section == null) {
            return false;
        }
        Matcher at = Pattern.compile(Pattern.quote(option) + "(?![\\w-])").matcher(section);
        while (at.find()) {
            if (at.start() == 0 || "-".indexOf(section.charAt(at.start() - 1)) < 0) {
                return true;
            }
        }
        return false;
    }

    /** The file cut at its own section markers, which is how {@code souther doc} cuts it too. */
    private static Map<String, String> sections() throws Exception {
        String text;
        try (InputStream in = AnOptionIsDocumentedUnderEveryCommandThatTakesItTest.class
                .getClassLoader().getResourceAsStream(RESOURCE)) {
            assertNotNull(in, RESOURCE);
            text = new String(in.readAllBytes(), StandardCharsets.UTF_8);
        }
        Map<String, String> sections = new LinkedHashMap<>();
        Matcher marker = SECTION.matcher(text);
        String name = null;
        int from = 0;
        while (marker.find()) {
            if (name != null) {
                sections.put(name, text.substring(from, marker.start()));
            }
            name = marker.group(1);
            from = marker.end();
        }
        if (name != null) {
            sections.put(name, text.substring(from));
        }
        return sections;
    }
}
