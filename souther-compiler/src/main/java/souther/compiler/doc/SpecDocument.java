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
 * <p>Every other name the document writes resolves too, to the section it stands in. An anchor may
 * sit on a paragraph, which is how the document points at a rule finer than a section; it is a
 * cross-reference target to AsciiDoc as much as a heading's is, and what comes back for it is the
 * section it stands in, that being the text there is to answer with.
 *
 * <p>A heading may also be asked for by names that are not anchors at all, written
 * {@code [also-named="e2015,e2016"]} beside its anchor. That is how several diagnostics explained
 * in one section are each asked for by their own code. It is a named attribute rather than a second
 * {@code [#...]} line because a heading has exactly one AsciiDoc ID: stacking anchors would leave
 * AsciiDoc reading the last one as the heading's ID and registering no target for the rest, while
 * this document read the first — the same heading under two identities, one of them invisible to
 * every renderer. A name Souther adds for its own lookup is therefore kept out of the ID.
 */
public final class SpecDocument {

    private static final String RESOURCE = "/META-INF/souther/specification.adoc";
    private static final Pattern ANCHOR = Pattern.compile("^\\[#([^\\]]+)]\\s*$");
    private static final Pattern ALSO_NAMED = Pattern.compile("^\\[also-named=\"([^\"]*)\"]\\s*$");
    /**
     * An anchor written into the line rather than above it — {@code [[id]]Text}. A rule stated as a
     * list item has nowhere to put a block anchor, so this is how one is named, and it names the
     * same kind of place: somewhere inside a section rather than a section.
     */
    private static final Pattern INLINE_ANCHOR = Pattern.compile("\\[\\[([a-zA-Z0-9_-]+)]]");
    private static final Pattern HEADING = Pattern.compile("^(={2,})\\s+(.*\\S)\\s*$");
    /**
     * The delimiter of a block AsciiDoc takes as it stands: listing {@code ----}, literal
     * {@code ....}, passthrough {@code ++++}, and the comment block {@code ////}. Four or more of
     * the character repeated, and the block runs to the line that repeats it exactly — a shorter
     * run, or a different character, is content rather than the end of it.
     */
    private static final Pattern OPAQUE_DELIMITER = Pattern.compile("^([-.+/])\\1{3,}$");

    /** A section: the first anchor written above its heading, its title, heading level (2 for
     *  {@code ==}), and body up to the next heading of the same or a higher level. */
    public record Section(String anchor, String title, int level, String body) {}

    /** Keyed by {@link DocName#canonical}: every name the document writes, and the section it
     *  resolves to. Several names may resolve to one section. */
    private final Map<String, Section> byAnchor;
    private final List<Section> inOrder;
    private final List<String> ownTexts;
    private final List<String> names;

    private SpecDocument(List<Section> sections, List<String> ownTexts,
            Map<String, Section> byAnchor, List<String> names) {
        this.inOrder = List.copyOf(sections);
        this.ownTexts = List.copyOf(ownTexts);
        this.byAnchor = Map.copyOf(byAnchor);
        this.names = List.copyOf(names);
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
        return bundled(Caller.CLI);
    }

    /** The same specification, with what it sends a reader to spelled the way {@code caller} asks. */
    static SpecDocument bundled(Caller caller) {
        try (InputStream in = SpecDocument.class.getResourceAsStream(RESOURCE)) {
            if (in == null) {
                throw new IllegalStateException("the bundled specification is missing: " + RESOURCE);
            }
            return of(new String(in.readAllBytes(), StandardCharsets.UTF_8), caller);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    public static SpecDocument of(String adoc) {
        return of(adoc, Caller.CLI);
    }

    static SpecDocument of(String adoc, Caller caller) {
        // Spelled before the document is cut into sections, so that what is ranked, cut to a
        // snippet and printed is one text rather than three readings of it.
        String[] lines = Affordance.materialize(adoc, caller).split("\n", -1);
        record Heading(List<String> anchors, String title, int level, int anchorFrom, int bodyFrom) {}
        boolean[] takenAsItStands = opaqueLines(lines);
        List<Heading> headings = new ArrayList<>();
        for (int i = 0; i < lines.length; i++) {
            if (takenAsItStands[i]) {
                continue;
            }
            Matcher heading = HEADING.matcher(lines[i]);
            if (!heading.matches() || i == 0) {
                continue;
            }
            // The attribute lines written above the heading belong to it: its anchor, which is the
            // name it is listed and printed under, and any further names it answers to.
            int anchorFrom = i;
            while (anchorFrom > 0 && (ANCHOR.matcher(lines[anchorFrom - 1]).matches()
                    || ALSO_NAMED.matcher(lines[anchorFrom - 1]).matches())) {
                anchorFrom--;
            }
            String own = null;
            List<String> anchors = new ArrayList<>();
            for (int a = anchorFrom; a < i; a++) {
                Matcher anchor = ANCHOR.matcher(lines[a]);
                if (anchor.matches()) {
                    if (own != null) {
                        // AsciiDoc would read the last of them as the heading's ID and register no
                        // target for the rest, leaving this document reading a name no renderer
                        // knows the heading by. A further name goes in `also-named`.
                        throw new IllegalStateException("a heading has one anchor, and `"
                                + heading.group(2) + "` is written with two: `" + own + "` and `"
                                + anchor.group(1) + "`");
                    }
                    own = anchor.group(1);
                    continue;
                }
                Matcher alsoNamed = ALSO_NAMED.matcher(lines[a]);
                alsoNamed.matches();
                for (String name : alsoNamed.group(1).split(",")) {
                    if (!name.isBlank()) {
                        anchors.add(name.strip());
                    }
                }
            }
            if (own == null) {
                continue;
            }
            anchors.addFirst(own);
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
        Section standingIn = null;
        int next = 0;
        for (int i = 0; i < lines.length; i++) {
            if (next < headings.size() && i == headings.get(next).anchorFrom()) {
                standingIn = sections.get(next);
                i = headings.get(next).bodyFrom() - 1;
                next++;
                continue;
            }
            if (takenAsItStands[i] || standingIn == null) {
                continue;
            }
            Matcher anchor = ANCHOR.matcher(lines[i]);
            if (anchor.matches()) {
                register(byAnchor, writtenAs, anchor.group(1), standingIn);
                continue;
            }
            Matcher inline = INLINE_ANCHOR.matcher(lines[i]);
            while (inline.find()) {
                register(byAnchor, writtenAs, inline.group(1), standingIn);
            }
        }
        return new SpecDocument(sections, ownTexts, byAnchor, List.copyOf(writtenAs.values()));
    }

    /**
     * Which lines are inside a block AsciiDoc takes as it stands, delimiters included.
     *
     * <p>Nothing there is document structure: a heading written in a listing is shown to a reader
     * as the words of a heading, and one written in a comment block is not shown at all. Reading
     * either as a section would not only answer for a name AsciiDoc never registered — it would cut
     * the surrounding section short at a heading that is not there, so the two would disagree about
     * where the sections are and not only about what they are called.
     *
     * <p>One walk answers for both what a heading is and what an anchor is, so the document has one
     * account of where its structure is written and not two that can come apart. That walk is
     * {@link TakenAsItStands}, which every reader of a document's structure shares — a shipped
     * markdown file and a part of one being cut off ask the same question about their own blocks.
     */
    private static boolean[] opaqueLines(String[] lines) {
        return TakenAsItStands.lines(lines);
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
     * Every name that resolves, as the document spells it, in the order the document writes them.
     *
     * <p>The same names {@link #section} answers for, so a caller suggesting what a reader might
     * have meant suggests from what they could have asked for. Suggesting from the sections alone
     * would leave a name that resolves out of reach of a near miss on it.
     */
    public List<String> names() {
        return names;
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
