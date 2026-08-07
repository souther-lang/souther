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
 *
 * <p>Every other name the document writes resolves too, to the section it stands in. A heading may
 * carry more than one anchor, which is how several diagnostics explained together are each asked
 * for by their own code; and an anchor may sit on a paragraph, which is how the document points at
 * a rule finer than a section. Neither is a section of its own — what comes back is the section the
 * name is written in — but a name the document sends a reader to is a name a reader can ask for.
 */
public final class SpecDocument {

    private static final String RESOURCE = "/META-INF/souther/specification.adoc";
    private static final Pattern ANCHOR = Pattern.compile("^\\[#([^\\]]+)]\\s*$");
    private static final Pattern HEADING = Pattern.compile("^(={2,})\\s+(.*\\S)\\s*$");
    private static final String LISTING_DELIMITER = "----";

    /** A section: the first anchor written above its heading, its title, heading level (2 for
     *  {@code ==}), and body up to the next heading of the same or a higher level. */
    public record Section(String anchor, String title, int level, String body) {}

    /** Keyed by {@link DocName#canonical}: every name the document writes, and the section it
     *  resolves to. Several names may resolve to one section. */
    private final Map<String, Section> byAnchor;
    private final List<Section> inOrder;
    private final List<String> ownTexts;

    private SpecDocument(List<Section> sections, List<String> ownTexts, Map<String, Section> byAnchor) {
        this.inOrder = List.copyOf(sections);
        this.ownTexts = List.copyOf(ownTexts);
        this.byAnchor = Map.copyOf(byAnchor);
    }

    /** Registers {@code anchor} as a name for {@code section}, refusing a name already taken. Two
     *  names that fold to one key would otherwise answer by whichever was read second. */
    private static void register(Map<String, Section> byAnchor, Map<String, String> writtenAs,
            String anchor, Section section) {
        String key = DocName.canonical(anchor);
        String taken = writtenAs.put(key, anchor);
        if (taken != null) {
            throw new IllegalStateException("two names to ask for fold together: `"
                    + taken + "` and `" + anchor + "`");
        }
        byAnchor.put(key, section);
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
        record Heading(List<String> anchors, String title, int level, int anchorFrom, int bodyFrom) {}
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
            if (!ANCHOR.matcher(lines[i - 1]).matches()) {
                continue;
            }
            // Every anchor written above the heading names it. The first one written is the
            // section's own name — the one it is listed and printed under — and the rest are
            // further names for the same section.
            int anchorFrom = i - 1;
            while (anchorFrom > 0 && ANCHOR.matcher(lines[anchorFrom - 1]).matches()) {
                anchorFrom--;
            }
            List<String> anchors = new ArrayList<>();
            for (int a = anchorFrom; a < i; a++) {
                Matcher anchor = ANCHOR.matcher(lines[a]);
                anchor.matches();
                anchors.add(anchor.group(1));
            }
            headings.add(new Heading(List.copyOf(anchors), heading.group(2), heading.group(1).length(),
                    anchorFrom, i + 1));
        }
        List<Section> sections = new ArrayList<>();
        List<String> ownTexts = new ArrayList<>();
        for (int h = 0; h < headings.size(); h++) {
            Heading here = headings.get(h);
            int end = lines.length;
            for (int n = h + 1; n < headings.size(); n++) {
                if (headings.get(n).level() <= here.level()) {
                    // The anchor lines belong to the next section, not to this body.
                    end = headings.get(n).anchorFrom();
                    break;
                }
            }
            // A subsection's words are its own: what this section itself says stops at the very
            // next heading, while the readable body runs on through its subsections.
            int ownEnd = h + 1 < headings.size() ? Math.min(end, headings.get(h + 1).anchorFrom()) : end;
            String body = String.join("\n", List.of(lines).subList(here.bodyFrom(), end)).strip();
            sections.add(new Section(here.anchors().getFirst(), here.title(), here.level(), body));
            ownTexts.add(String.join("\n", List.of(lines).subList(here.bodyFrom(), ownEnd)).strip());
        }
        Map<String, Section> byAnchor = new LinkedHashMap<>();
        Map<String, String> writtenAs = new LinkedHashMap<>();
        for (int h = 0; h < headings.size(); h++) {
            for (String anchor : headings.get(h).anchors()) {
                register(byAnchor, writtenAs, anchor, sections.get(h));
            }
        }
        // An anchor written anywhere else names a place inside a section rather than a section, and
        // there is no text of its own to answer with: what a reader is sent to for it is the
        // section it stands in. The heading runs are stepped over, having been registered above.
        inListing = false;
        Section standingIn = null;
        int next = 0;
        for (int i = 0; i < lines.length; i++) {
            if (next < headings.size() && i == headings.get(next).anchorFrom()) {
                standingIn = sections.get(next);
                i = headings.get(next).bodyFrom() - 1;
                next++;
                continue;
            }
            if (lines[i].startsWith(LISTING_DELIMITER)) {
                inListing = !inListing;
                continue;
            }
            if (inListing || standingIn == null) {
                continue;
            }
            Matcher anchor = ANCHOR.matcher(lines[i]);
            if (anchor.matches()) {
                register(byAnchor, writtenAs, anchor.group(1), standingIn);
            }
        }
        return new SpecDocument(sections, ownTexts, byAnchor);
    }

    /** Every section, in document order. */
    public List<Section> sections() {
        return inOrder;
    }

    /** The section named by {@code anchor} in whatever case it was asked for, or null when no
     *  section has that anchor. */
    public Section section(String anchor) {
        return byAnchor.get(DocName.canonical(anchor));
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
