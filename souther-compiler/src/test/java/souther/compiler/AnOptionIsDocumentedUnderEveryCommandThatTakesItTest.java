package souther.compiler;

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
