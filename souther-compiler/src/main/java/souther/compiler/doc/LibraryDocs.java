package souther.compiler.doc;

import java.io.IOException;
import java.io.InputStream;
import java.io.UncheckedIOException;
import java.net.URL;
import java.nio.charset.StandardCharsets;
import java.util.ArrayList;
import java.util.Enumeration;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Documentation a dependency ships inside its own jar, under {@code META-INF/souther-docs/}.
 *
 * <p>Each contributing jar carries a {@code sets} registry naming its doc sets, and per set an
 * {@code index} listing the topic files. The docs therefore version with the jar they describe:
 * bundling a different raoh bundles that raoh's docs, and no copy is maintained anywhere else.
 *
 * <p>A file may also name parts of itself, by writing {@code <!-- souther-section: name -->} on the
 * line above a heading. That name is then asked for as {@code set/topic/name}, and it is the doc
 * set's to keep: the specification's sections are addressable because every heading carries an
 * explicit anchor, not because anything reads structure out of the prose. Deriving a name from a
 * heading instead would publish an identifier that moves when the heading is reworded, renumbered
 * or translated, and a name a client has written down is not the doc set's to move.
 *
 * <p>A file that names no part of itself is one document, whole. That is the honest answer for a
 * jar this compiler does not author: what it has to offer is the file its index promised, and a
 * name invented here would be Souther's, published as though it were raoh's.
 */
public final class LibraryDocs {

    private static final String ROOT = "META-INF/souther-docs/";

    /** A name a doc set gives to a part of one of its files, written above the heading it opens. */
    private static final Pattern DECLARED = Pattern.compile(
            "^<!--\\s*souther-section:\\s*([A-Za-z0-9][A-Za-z0-9._-]*)\\s*-->\\s*$");

    private static final Pattern HEADING = Pattern.compile("^(#{1,6})\\s+(\\S.*?)\\s*$");

    /**
     * One document, or one part of one that its doc set has named.
     *
     * <p>{@code from} and {@code to} are where the text of it is in the file: the whole of it for a
     * document, and for a named part, its heading through to the next heading that closes it. A
     * part carries its subordinate parts the way a specification section carries its subsections,
     * so asking for the larger thing is asking for all of it.
     *
     * <p>{@code depth} is 0 for a document and the heading's level for a part of one, which is what
     * a listing indents by. {@code listedFor} is null for a topic every caller is shown, which is
     * nearly all of them. A topic that documents an interface only one caller has is named in that
     * caller's listing alone: the listing is where a client with no other map of what is here
     * decides what to read, and a manual for a wire this one is not on is not an answer it can use.
     * It stays readable by name, because what the toolchain is remains worth knowing to a reader
     * who asks.
     */
    public record Topic(String name, String title, int depth, String resource, int from, int to,
            Caller listedFor) {

        /** Whether {@code caller}'s listing names this topic. */
        boolean listedFor(Caller caller) {
            return listedFor == null || listedFor == caller;
        }
    }

    private final ClassLoader loader;
    /** Keyed by {@link DocName#canonical}, so a topic is found in whatever case it is asked for.
     *  The topic keeps its own spelling: the name is also the path its text is read from. */
    private final Map<String, Topic> byName;
    /**
     * What a search ranks: the named parts of a file that has them, and the file itself otherwise.
     *
     * <p>Ranking both would answer one occurrence twice, and a search that says a thing twice is a
     * search with fewer answers in the room it has. Where a file names its parts, the part is the
     * smaller true answer, and it is the one a reader is sent to.
     */
    private final List<Topic> ranked;
    /** Who the text is spelled for, wherever it sends its reader somewhere. */
    private final Caller caller;

    private LibraryDocs(ClassLoader loader, Map<String, Topic> byName, List<Topic> ranked,
            Caller caller) {
        this.loader = loader;
        this.byName = byName;
        this.ranked = ranked;
        this.caller = caller;
    }

    /** The doc sets reachable through {@code loader} — for the CLI, everything bundled with it. */
    public static LibraryDocs on(ClassLoader loader) {
        return on(loader, Caller.CLI);
    }

    /** The same sets, read as {@code caller} is to be answered. */
    static LibraryDocs on(ClassLoader loader, Caller caller) {
        Map<String, Topic> byName = new LinkedHashMap<>();
        List<Topic> ranked = new ArrayList<>();
        try {
            Enumeration<URL> registries = loader.getResources(ROOT + "sets");
            while (registries.hasMoreElements()) {
                for (String set : lines(registries.nextElement())) {
                    String index = ROOT + set + "/index";
                    URL indexUrl = loader.getResource(index);
                    if (indexUrl == null) {
                        continue;
                    }
                    for (String entry : lines(indexUrl)) {
                        // A file, and after a tab the caller whose listing names it. An index that
                        // writes only the file names every caller's listing, which is what a doc
                        // set that has never had to think about wires writes.
                        String[] written = entry.split("\t", 2);
                        String file = written[0].strip();
                        String topic = set + "/" + file.replaceFirst("\\.md$", "");
                        String resource = ROOT + set + "/" + file;
                        Caller listedFor = written.length < 2
                                ? null : listedFor(written[1].strip(), topic);
                        String text = Affordance.materialize(text(loader, resource), caller);
                        register(byName, new Topic(topic, titleOf(text, file), 0, resource,
                                0, text.length(), listedFor));
                        List<Topic> parts = named(topic, resource, text, listedFor);
                        parts.forEach(part -> register(byName, part));
                        // The parts where there are parts, and the file itself where there are not.
                        ranked.addAll(parts.isEmpty()
                                ? List.of(byName.get(DocName.canonical(topic))) : parts);
                    }
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return new LibraryDocs(loader, byName, List.copyOf(ranked), caller);
    }

    private static void register(Map<String, Topic> byName, Topic topic) {
        Topic taken = byName.put(DocName.canonical(topic.name()), topic);
        if (taken != null) {
            throw new IllegalStateException("two shipped topics are asked for by the same name: `"
                    + taken.name() + "` and `" + topic.name() + "`");
        }
    }

    /**
     * The parts {@code text} names of itself, each running to the heading that closes it.
     *
     * <p>A declaration that opens nothing is a mistake in the doc set rather than a part with no
     * text: the name would be published, answered with whatever followed it, and moved the next
     * time the file was edited. It is refused where the set is read.
     */
    private static List<Topic> named(String topic, String resource, String text, Caller listedFor) {
        // Every heading, whether the file names it or not: what closes a part is the next heading
        // that is not under it, and a heading the set chose not to name still is not under it.
        record Head(String name, String title, int level, int from) {}
        List<Head> heads = new ArrayList<>();
        String[] lines = text.split("\n", -1);
        int[] starts = new int[lines.length];
        for (int i = 0, at = 0; i < lines.length; i++) {
            starts[i] = at;
            at += lines[i].length() + 1;
        }
        for (int i = 0; i < lines.length; i++) {
            Matcher declaration = DECLARED.matcher(lines[i]);
            if (declaration.matches()) {
                Matcher heading = i + 1 < lines.length ? HEADING.matcher(lines[i + 1]) : null;
                if (heading == null || !heading.matches()) {
                    throw new IllegalStateException("`" + topic + "` names a section `"
                            + declaration.group(1) + "` above something that is not a heading");
                }
                heads.add(new Head(topic + "/" + declaration.group(1), heading.group(2),
                        heading.group(1).length(), starts[i]));
                i++;
                continue;
            }
            Matcher heading = HEADING.matcher(lines[i]);
            if (heading.matches()) {
                heads.add(new Head(null, heading.group(2), heading.group(1).length(), starts[i]));
            }
        }
        List<Topic> parts = new ArrayList<>();
        for (int h = 0; h < heads.size(); h++) {
            Head here = heads.get(h);
            if (here.name() == null) {
                continue;
            }
            int to = text.length();
            for (int n = h + 1; n < heads.size(); n++) {
                if (heads.get(n).level() <= here.level()) {
                    to = heads.get(n).from();
                    break;
                }
            }
            parts.add(new Topic(here.name(), here.title(), here.level(), resource,
                    here.from(), to, listedFor));
        }
        return parts;
    }

    /** The caller an index names beside a topic, refusing one no caller answers to. */
    private static Caller listedFor(String written, String topic) {
        for (Caller caller : Caller.values()) {
            if (caller.name().equalsIgnoreCase(written)) {
                return caller;
            }
        }
        throw new IllegalStateException("`" + topic + "` is listed for `" + written
                + "`, which is nobody this answers");
    }

    /** Every shipped topic, in registry order. */
    public List<Topic> topics() {
        return List.copyOf(byName.values());
    }

    /**
     * The text of {@code set/topic}, or null when nothing ships under that name — including when
     * an index names a file the jar does not carry, which is a broken doc set rather than a topic
     * with nothing in it.
     */
    public String read(String name) {
        Topic topic = byName.get(DocName.canonical(name));
        if (topic == null || loader.getResource(topic.resource()) == null) {
            return null;
        }
        return text(topic);
    }

    /** Every topic whose title or text contains {@code term}, case-insensitively. */
    public List<Topic> search(String term) {
        return rank(term).stream().map(Hit::topic).toList();
    }

    /** A topic the term was found in, scored the same way a specification section is. */
    public record Hit(Topic topic, boolean titled, int occurrences, String snippet) {}

    /**
     * The topics that say {@code term}, each with what a caller needs to rank it against a
     * specification section: whether the title names it, how often it is said, and the line it was
     * found on.
     */
    public List<Hit> rank(String term) {
        if (term == null || term.isBlank()) {
            return List.of();
        }
        String needle = term.toLowerCase();
        List<Hit> hits = new ArrayList<>();
        for (Topic topic : ranked) {
            String body = text(topic);
            boolean titled = topic.title().toLowerCase().contains(needle)
                    || topic.name().toLowerCase().contains(needle);
            int occurrences = count(body.toLowerCase(), needle);
            if (titled || occurrences > 0) {
                hits.add(new Hit(topic, titled, occurrences, snippet(topic, term)));
            }
        }
        return hits;
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

    /** The line of {@code topic} that says {@code term}, cut to a readable width. */
    public String snippet(Topic topic, String term) {
        String needle = term.toLowerCase();
        String line = text(topic).lines()
                .map(String::strip)
                .filter(l -> !l.isEmpty() && !l.startsWith("#") && !l.startsWith("|"))
                .filter(l -> l.toLowerCase().contains(needle))
                .findFirst()
                .orElse("");
        return line.length() <= 120 ? line : line.substring(0, 119) + "…";
    }

    private static String titleOf(String text, String fallback) {
        return text.lines()
                .filter(l -> l.startsWith("# "))
                .map(l -> l.substring(2).strip())
                .findFirst()
                .orElse(fallback);
    }

    /**
     * The text of {@code topic} as this reader is to be shown it.
     *
     * <p>Spelled here rather than where it is printed, because a search ranks and cuts snippets
     * from the same text. A term that named the other caller's spelling would otherwise match, and
     * the snippet it matched in would hand back the operation this reader cannot carry out. The
     * extent is measured against the same spelling, so it is taken after it and not before.
     */
    private String text(Topic topic) {
        String text = Affordance.materialize(text(loader, topic.resource()), caller);
        return topic.from() == 0 && topic.to() >= text.length()
                ? text : text.substring(topic.from(), Math.min(topic.to(), text.length()));
    }

    private static String text(ClassLoader loader, String resource) {
        try (InputStream in = loader.getResourceAsStream(resource)) {
            if (in == null) {
                return "";
            }
            return new String(in.readAllBytes(), StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static List<String> lines(URL url) throws IOException {
        try (InputStream in = url.openStream()) {
            return new String(in.readAllBytes(), StandardCharsets.UTF_8).lines()
                    .map(String::strip)
                    .filter(l -> !l.isEmpty())
                    .toList();
        }
    }
}
