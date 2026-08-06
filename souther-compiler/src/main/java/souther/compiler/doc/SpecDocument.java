package souther.compiler.doc;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * The language specification, read back as its sections.
 *
 * <p>Every heading in specification.adoc carries an explicit {@code [#anchor]} on the line above
 * it; the anchor is the name a section is asked for by, the same name cross-references inside the
 * document use.
 */
public final class SpecDocument {

    private static final String RESOURCE = "/META-INF/souther/specification.adoc";
    private static final Pattern ANCHOR = Pattern.compile("^\\[#([^\\]]+)]\\s*$");
    private static final Pattern HEADING = Pattern.compile("^(={2,})\\s+(.*\\S)\\s*$");
    private static final String LISTING_DELIMITER = "----";

    /** A section: its anchor, title, heading level (2 for {@code ==}), and body up to the next heading of the same or a higher level. */
    public record Section(String anchor, String title, int level, String body) {}

    private final Map<String, Section> byAnchor;
    private final List<Section> inOrder;
    private final List<String> ownTexts;

    private SpecDocument(List<Section> sections, List<String> ownTexts) {
        this.inOrder = List.copyOf(sections);
        this.ownTexts = List.copyOf(ownTexts);
        this.byAnchor = new LinkedHashMap<>();
        for (Section s : sections) {
            byAnchor.put(s.anchor(), s);
        }
    }

    /** The specification this compiler was built from, bundled in its jar. */
    public static SpecDocument bundled() {
        try (InputStream in = SpecDocument.class.getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException("the bundled specification is missing: " + RESOURCE);
            }
            return of(new String(in.readAllBytes(), StandardCharsets.UTF_8));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    public static SpecDocument of(String adoc) {
        String[] lines = adoc.split("\n", -1);
        record Heading(String anchor, String title, int level, int bodyFrom) {}
        List<Heading> headings = new ArrayList<>();
        boolean inListing = false;
        for (int i = 0; i < lines.length; i++) {
            if (lines[i].startsWith(LISTING_DELIMITER)) {
                inListing = !inListing;
                continue;
            }
            if (inListing) {
                continue;
            }
            Matcher heading = HEADING.matcher(lines[i]);
            if (!heading.matches() || i == 0) {
                continue;
            }
            Matcher anchor = ANCHOR.matcher(lines[i - 1]);
            if (!anchor.matches()) {
                continue;
            }
            headings.add(new Heading(anchor.group(1), heading.group(2), heading.group(1).length(), i + 1));
        }
        List<Section> sections = new ArrayList<>();
        List<String> ownTexts = new ArrayList<>();
        for (int h = 0; h < headings.size(); h++) {
            Heading here = headings.get(h);
            int end = lines.length;
            for (int n = h + 1; n < headings.size(); n++) {
                if (headings.get(n).level() <= here.level()) {
                    // The anchor line belongs to the next section, not to this body.
                    end = headings.get(n).bodyFrom() - 2;
                    break;
                }
            }
            // A subsection's words are its own: what this section itself says stops at the very
            // next heading, while the readable body runs on through its subsections.
            int ownEnd = h + 1 < headings.size() ? Math.min(end, headings.get(h + 1).bodyFrom() - 2) : end;
            String body = String.join("\n", List.of(lines).subList(here.bodyFrom(), end)).strip();
            sections.add(new Section(here.anchor(), here.title(), here.level(), body));
            ownTexts.add(String.join("\n", List.of(lines).subList(here.bodyFrom(), ownEnd)).strip());
        }
        return new SpecDocument(sections, ownTexts);
    }

    /** Every section, in document order. */
    public List<Section> sections() {
        return inOrder;
    }

    /** The section named by {@code anchor}, or null when no section has that anchor. */
    public Section section(String anchor) {
        return byAnchor.get(anchor);
    }

    /**
     * Every section whose title or own prose contains {@code term}, case-insensitively, in
     * document order. A word said only inside a subsection answers as that subsection.
     */
    public List<Section> search(String term) {
        return rank(term).stream().map(Hit::section).toList();
    }

    /**
     * A section the term was found in: whether its title names it, how often it says it, and the
     * line it was found on. The line is what makes a list of hits an answer rather than a filtered
     * table of contents — without it a reader has to open each section to tell a hit from a
     * coincidence.
     */
    public record Hit(Section section, boolean titled, int occurrences, String snippet) {}

    /** How wide a snippet may run before it stops being readable in a list. */
    private static final int SNIPPET_WIDTH = 120;

    /**
     * The sections that say {@code term}, best answer first: a section titled with the term, then
     * the sections that dwell on it most. A word common enough to appear across the specification
     * is otherwise no answer at all — over half the document comes back and nothing is chosen.
     */
    public List<Hit> rank(String term) {
        // A term of no characters sits at every position and matches everything, which is not an
        // answer; a walk over its occurrences would also never advance past one.
        if (term == null || term.isBlank()) {
            return List.of();
        }
        String needle = term.toLowerCase();
        List<Hit> hits = new ArrayList<>();
        for (int i = 0; i < inOrder.size(); i++) {
            Section s = inOrder.get(i);
            boolean titled = s.title().toLowerCase().contains(needle);
            String own = ownTexts.get(i);
            int occurrences = count(own.toLowerCase(), needle);
            if (titled || occurrences > 0) {
                hits.add(new Hit(s, titled, occurrences, snippet(own, needle)));
            }
        }
        return hits.stream()
                .sorted(java.util.Comparator.comparing(Hit::titled).reversed()
                        .thenComparing(java.util.Comparator.comparingInt(Hit::occurrences).reversed()))
                .toList();
    }

    /**
     * The line {@code needle} was found on, trimmed of the AsciiDoc that carries no meaning aloud
     * and cut to a readable width around the term. A section matched only by its title falls back
     * to its opening line, which is what it is about.
     */
    private static String snippet(String body, String needle) {
        String line = body.lines()
                .map(String::strip)
                .filter(l -> !l.isEmpty() && !l.startsWith("|") && !l.startsWith("["))
                .filter(l -> l.toLowerCase().contains(needle))
                .findFirst()
                .orElseGet(() -> body.lines().map(String::strip)
                        .filter(l -> !l.isEmpty() && !l.startsWith("[") && !l.startsWith("|"))
                        .findFirst().orElse(""));
        String plain = line.replace("`+", "`").replace("+`", "`").replaceAll("<<([^,>]+)[^>]*>>", "$1");
        if (plain.length() <= SNIPPET_WIDTH) {
            return plain;
        }
        int at = plain.toLowerCase().indexOf(needle);
        int from = at < 0 ? 0 : Math.max(0, at - SNIPPET_WIDTH / 3);
        int to = Math.min(plain.length(), from + SNIPPET_WIDTH);
        return (from > 0 ? "…" : "") + plain.substring(from, to).strip() + (to < plain.length() ? "…" : "");
    }

    private static int count(String haystack, String needle) {
        if (needle.isEmpty()) {
            return 0;
        }
        int n = 0;
        for (int at = haystack.indexOf(needle); at >= 0; at = haystack.indexOf(needle, at + needle.length())) {
            n++;
        }
        return n;
    }
}
