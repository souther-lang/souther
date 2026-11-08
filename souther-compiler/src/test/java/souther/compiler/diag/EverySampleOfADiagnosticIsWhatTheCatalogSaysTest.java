package souther.compiler.diag;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.List;
import java.util.Properties;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the specification shows a diagnostic printing is a sentence the catalog writes.
 *
 * <p>A section named for a code shows its diagnostic in a {@code [,text]} block, and a reader takes
 * that block as what the compiler prints. Nothing printed it: it was written by hand beside the
 * catalog entry, so a change to the entry left the sample saying what the compiler no longer says,
 * and nothing noticed. Here every sentence of such a block is held to the catalog: with each
 * placeholder of an entry standing for any text, the sentence is one of the entries.
 *
 * <p>What a block shows besides sentences is told apart by its form and is not held to anything:
 * the quoted source and the caret under it, the title line, a {@code file:line:col} location, and
 * the {@code found:} and {@code expected:} lines of a comparison.
 */
class EverySampleOfADiagnosticIsWhatTheCatalogSaysTest {

    private static final String SPEC = "/META-INF/souther/specification.adoc";
    private static final String CATALOG = "/souther/compiler/diag/messages.properties";

    private static final Pattern CODE_SECTION = Pattern.compile("^\\[#e[0-9]{4}]$");
    private static final Pattern ANY_ANCHOR = Pattern.compile("^\\[#[a-z0-9-]+]$");
    private static final Pattern PLACEHOLDER = Pattern.compile("\\{[A-Za-z0-9]+}");
    /** A line that starts a sentence of its own: a hint or a note under the message. */
    private static final Pattern PREFIX = Pattern.compile("^\\s*(?:Hint|hint|Note|note):\\s*");
    /** What a block shows that is not a sentence of the catalog. */
    private static final Pattern NOT_A_SENTENCE = Pattern.compile(
            "^\\s*(?:[0-9]+\\s*\\||\\^|-- |found:|expected:|[\\w./-]+\\.sou:[0-9]+:[0-9]+$)");
    /** An entry whose own words are fewer than this matches nearly any sentence, so it is not one a
     *  sample can be told to be. */
    private static final int FEWEST_OWN_CHARACTERS = 5;

    @Test
    void everySentenceASampleShowsIsOneTheCatalogWrites() throws IOException {
        List<Pattern> entries = entries();
        List<String> unwritten = new ArrayList<>();
        for (Sentence sentence : sentencesOfSamples(spec())) {
            if (entries.stream().noneMatch(entry -> entry.matcher(sentence.text()).matches())) {
                unwritten.add(sentence.section() + " line " + sentence.line() + ": " + sentence.text());
            }
        }
        assertEquals(List.of(), unwritten,
                "a sample shows a sentence the compiler does not print; write the catalog's");
    }

    private record Sentence(String section, int line, String text) {}

    /** The sentences of every {@code [,text]} block in a section named for a code, a sentence being
     *  a line and the lines that continue it, up to a blank line or one that starts its own. */
    private static List<Sentence> sentencesOfSamples(String spec) {
        String[] lines = spec.split("\\R", -1);
        List<Sentence> found = new ArrayList<>();
        String section = null;
        for (int i = 0; i < lines.length; i++) {
            if (CODE_SECTION.matcher(lines[i]).matches()) {
                section = lines[i].substring(2, lines[i].length() - 1);
            } else if (ANY_ANCHOR.matcher(lines[i]).matches()) {
                section = null;
            }
            if (section == null || !lines[i].equals("[,text]") || i + 1 >= lines.length
                    || !lines[i + 1].equals("----")) {
                continue;
            }
            int at = i + 2;
            StringBuilder text = null;
            int startedAt = 0;
            for (; at < lines.length && !lines[at].equals("----"); at++) {
                String line = lines[at];
                boolean ownStart = PREFIX.matcher(line).find();
                if (line.isBlank() || NOT_A_SENTENCE.matcher(line).find() || ownStart) {
                    if (text != null) {
                        found.add(new Sentence(section, startedAt, text.toString()));
                        text = null;
                    }
                    if (!ownStart) {
                        continue;
                    }
                }
                String said = PREFIX.matcher(line).replaceFirst("").strip();
                if (text == null) {
                    text = new StringBuilder(said);
                    startedAt = at + 1;
                } else {
                    text.append(' ').append(said);
                }
            }
            if (text != null) {
                found.add(new Sentence(section, startedAt, text.toString()));
            }
            i = at;
        }
        return found;
    }

    /** Each catalog entry as the sentences it can print: its placeholders stand for any text. */
    private static List<Pattern> entries() throws IOException {
        Properties catalog = new Properties();
        try (InputStream in = EverySampleOfADiagnosticIsWhatTheCatalogSaysTest.class
                .getResourceAsStream(CATALOG)) {
            catalog.load(new InputStreamReader(in, StandardCharsets.UTF_8));
        }
        List<Pattern> entries = new ArrayList<>();
        for (String key : catalog.stringPropertyNames()) {
            String[] own = PLACEHOLDER.split(printed(catalog.getProperty(key)), -1);
            if (String.join("", own).replaceAll("\\s", "").length() < FEWEST_OWN_CHARACTERS) {
                continue;
            }
            List<String> quoted = new ArrayList<>();
            for (String part : own) {
                quoted.add(Pattern.quote(part));
            }
            entries.add(Pattern.compile(String.join(".+?", quoted), Pattern.DOTALL));
        }
        return entries;
    }

    /** The entry as it prints: a positional entry is a MessageFormat pattern, whose doubled
     *  apostrophe is one and whose quoted brace is a brace, and a named entry writes a brace of its
     *  own doubled. */
    private static String printed(String entry) {
        return entry.replace("'{'", "{").replace("'}'", "}").replace("''", "'")
                .replace("{{", "{").replace("}}", "}");
    }

    private static String spec() throws IOException {
        try (InputStream in = EverySampleOfADiagnosticIsWhatTheCatalogSaysTest.class
                .getResourceAsStream(SPEC)) {
            if (in == null) {
                throw new IllegalStateException("the bundled specification is missing: " + SPEC);
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        }
    }
}
