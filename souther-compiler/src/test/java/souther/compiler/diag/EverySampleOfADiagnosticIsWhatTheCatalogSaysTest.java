package souther.compiler.diag;

import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.nio.charset.StandardCharsets;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Properties;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.msg.Code;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.MessageCodes;
import souther.compiler.diag.msg.MessageKeys;

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
    /** A line of quoted source, or the caret under one. */
    private static final Pattern SOURCE = Pattern.compile("^\\s*(?:[0-9]+\\s*\\||\\^)");
    /** What a block shows that is not a sentence of the catalog. */
    private static final Pattern NOT_A_SENTENCE = Pattern.compile(
            "^\\s*(?:[0-9]+\\s*\\||\\^|-- |found:|expected:|[\\w./-]+\\.sou:[0-9]+:[0-9]+$)");
    /** An entry whose own words are fewer than this matches nearly any sentence, so it is not one a
     *  sample can be told to be. */
    private static final int FEWEST_OWN_CHARACTERS = 5;

    @Test
    void everySentenceASampleShowsIsOneTheCatalogWrites() throws IOException {
        List<Entry> entries = entries();
        List<String> unwritten = new ArrayList<>();
        for (Sentence sentence : sentencesOfSamples(spec())) {
            if (entries.stream().noneMatch(entry -> entry.writes(sentence.text()))) {
                unwritten.add(sentence.section() + " line " + sentence.line() + ": " + sentence.text());
            }
        }
        assertEquals(List.of(), unwritten,
                "a sample shows a sentence the compiler does not print; write the catalog's");
    }

    /**
     * And the sentence a sample opens with is one its code reports: a sample showing what another
     * code reports would be a sentence the catalog writes and still not what this diagnostic prints.
     *
     * <p>A sample is of the section's code unless the paragraph introducing it names the codes it
     * is of, as a section about several codes does ("E2015 leaves a clause …"). What a sample opens
     * with is its first sentence that is not a label under the quoted source.
     */
    @Test
    void aSampleOpensWithWhatItsCodeReports() throws IOException {
        List<Entry> entries = entries();
        Map<String, Set<String>> reportedBy = reportedByCode();
        List<String> elsewhere = new ArrayList<>();
        for (Sentence sentence : sentencesOfSamples(spec())) {
            if (!sentence.opens()) {
                continue;
            }
            Set<String> own = new TreeSet<>();
            for (String code : sentence.codes()) {
                own.addAll(reportedBy.getOrDefault(code, Set.of()));
            }
            if (entries.stream().noneMatch(entry -> own.contains(entry.key())
                    && entry.writes(sentence.text()))) {
                elsewhere.add(sentence.section() + " line " + sentence.line() + ": "
                        + sentence.text());
            }
        }
        assertEquals(List.of(), elsewhere,
                "a sample opens with a sentence its code does not report");
    }

    /** The catalog key of every message that reports a rule, by the section its code is named for. */
    private static Map<String, Set<String>> reportedByCode() {
        Map<String, Set<String>> by = new TreeMap<>();
        Deque<Class<?>> open = new ArrayDeque<>(List.of(Message.class));
        while (!open.isEmpty()) {
            Class<?> each = open.pop();
            if (each.isSealed()) {
                open.addAll(List.of(each.getPermittedSubclasses()));
            } else if (each.isRecord() && each.isAnnotationPresent(Code.class)) {
                by.computeIfAbsent(MessageCodes.of(each).name().toLowerCase(Locale.ROOT),
                        _ -> new TreeSet<>()).add(MessageKeys.of(each));
            }
        }
        return by;
    }

    /** A sentence of a sample, the codes the sample is of, and whether it is the one the sample
     *  opens with. */
    private record Sentence(String section, Set<String> codes, int line, String text,
                            boolean opens) {}

    /** A code named in prose, as {@code E2015}. */
    private static final Pattern A_CODE = Pattern.compile("\\bE([0-9]{4})\\b");

    /** The codes the paragraph just above line {@code at} names, or the section's where it names
     *  none. */
    private static Set<String> codesOf(String[] lines, int at, String section) {
        int above = at - 1;
        while (above >= 0 && lines[above].isBlank()) {
            above--;
        }
        Set<String> named = new TreeSet<>();
        for (; above >= 0 && !lines[above].isBlank() && !lines[above].startsWith("[")
                && !lines[above].startsWith("="); above--) {
            Matcher code = A_CODE.matcher(lines[above]);
            while (code.find()) {
                named.add("e" + code.group(1));
            }
        }
        return named.isEmpty() ? Set.of(section) : named;
    }

    /** A catalog entry as the sentences it can print. What comes before its first placeholder is
     *  how every one of them starts, so a sentence that does not start so is not matched against
     *  the rest. */
    private record Entry(String key, String opening, Pattern sentences) {
        boolean writes(String sentence) {
            return sentence.startsWith(opening) && sentences.matcher(sentence).matches();
        }
    }

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
            Set<String> codes = codesOf(lines, i, section);
            int at = i + 2;
            StringBuilder text = null;
            int startedAt = 0;
            boolean opens = false;
            boolean opened = false;
            boolean underSource = false;
            for (; at < lines.length && !lines[at].equals("----"); at++) {
                String line = lines[at];
                boolean ownStart = PREFIX.matcher(line).find();
                boolean source = SOURCE.matcher(line).find();
                if (line.isBlank() || NOT_A_SENTENCE.matcher(line).find() || ownStart) {
                    if (text != null) {
                        found.add(new Sentence(section, codes, startedAt, text.toString(), opens));
                        text = null;
                    }
                    if (!ownStart) {
                        underSource = source || (underSource && !line.isBlank());
                        continue;
                    }
                }
                String said = PREFIX.matcher(line).replaceFirst("").strip();
                if (text == null) {
                    text = new StringBuilder(said);
                    startedAt = at + 1;
                    // A sentence right under the quoted source is a label of it, not the message.
                    opens = !opened && !ownStart && !underSource;
                    opened = opened || opens;
                } else {
                    text.append(' ').append(said);
                }
            }
            if (text != null) {
                found.add(new Sentence(section, codes, startedAt, text.toString(), opens));
            }
            i = at;
        }
        return found;
    }

    /** Each catalog entry as the sentences it can print: its placeholders stand for any text. */
    private static List<Entry> entries() throws IOException {
        Properties catalog = new Properties();
        try (InputStream in = EverySampleOfADiagnosticIsWhatTheCatalogSaysTest.class
                .getResourceAsStream(CATALOG)) {
            catalog.load(new InputStreamReader(in, StandardCharsets.UTF_8));
        }
        List<Entry> entries = new ArrayList<>();
        for (String key : catalog.stringPropertyNames()) {
            String[] own = PLACEHOLDER.split(printed(catalog.getProperty(key)), -1);
            if (String.join("", own).replaceAll("\\s", "").length() < FEWEST_OWN_CHARACTERS) {
                continue;
            }
            List<String> quoted = new ArrayList<>();
            for (String part : own) {
                quoted.add(Pattern.quote(part));
            }
            entries.add(new Entry(key, own[0],
                    Pattern.compile(String.join(".+?", quoted), Pattern.DOTALL)));
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
