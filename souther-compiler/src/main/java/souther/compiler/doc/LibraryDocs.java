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

/**
 * Documentation a dependency ships inside its own jar, under {@code META-INF/souther-docs/}.
 *
 * <p>Each contributing jar carries a {@code sets} registry naming its doc sets, and per set an
 * {@code index} listing the topic files. The docs therefore version with the jar they describe:
 * bundling a different raoh bundles that raoh's docs, and no copy is maintained anywhere else.
 */
public final class LibraryDocs {

    private static final String ROOT = "META-INF/souther-docs/";

    /**
     * One shipped document: {@code set/topic} as the jar that ships it spells the name, the title
     * of its first markdown heading, where its text is, and the one caller whose listing names it.
     *
     * <p>{@code listedFor} is null for a topic every caller is shown, which is nearly all of them.
     * A topic that documents an interface only one caller has is named in that caller's listing
     * alone: the listing is where a client with no other map of what is here decides what to read,
     * and a manual for a wire this one is not on is not an answer it can use. It stays readable by
     * name, because what the toolchain is remains worth knowing to a reader who asks.
     */
    public record Topic(String name, String title, String resource, Caller listedFor) {

        /** Whether {@code caller}'s listing names this topic. */
        boolean listedFor(Caller caller) {
            return listedFor == null || listedFor == caller;
        }
    }

    private final ClassLoader loader;
    /** Keyed by {@link DocName#canonical}, so a topic is found in whatever case it is asked for.
     *  The topic keeps its own spelling: the name is also the path its text is read from. */
    private final Map<String, Topic> byName;
    /** Who the text is spelled for, wherever it sends its reader somewhere. */
    private final Caller caller;

    private LibraryDocs(ClassLoader loader, Map<String, Topic> byName, Caller caller) {
        this.loader = loader;
        this.byName = byName;
        this.caller = caller;
    }

    /** The doc sets reachable through {@code loader} — for the CLI, everything bundled with it. */
    public static LibraryDocs on(ClassLoader loader) {
        return on(loader, Caller.CLI);
    }

    /** The same sets, read as {@code caller} is to be answered. */
    static LibraryDocs on(ClassLoader loader, Caller caller) {
        Map<String, Topic> byName = new LinkedHashMap<>();
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
                        Topic taken = byName.put(DocName.canonical(topic),
                                new Topic(topic, titleOf(loader, resource, file, caller), resource,
                                        written.length < 2 ? null : listedFor(written[1].strip(), topic)));
                        if (taken != null) {
                            throw new IllegalStateException(
                                    "two shipped topics are asked for by the same name: `"
                                            + taken.name() + "` and `" + topic + "`");
                        }
                    }
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return new LibraryDocs(loader, byName, caller);
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
        return text(topic.resource());
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
        for (Topic topic : byName.values()) {
            String body = text(topic.resource());
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
        String line = text(topic.resource()).lines()
                .map(String::strip)
                .filter(l -> !l.isEmpty() && !l.startsWith("#") && !l.startsWith("|"))
                .filter(l -> l.toLowerCase().contains(needle))
                .findFirst()
                .orElse("");
        return line.length() <= 120 ? line : line.substring(0, 119) + "…";
    }

    private static String titleOf(ClassLoader loader, String resource, String fallback, Caller caller) {
        return Affordance.materialize(text(loader, resource), caller).lines()
                .filter(l -> l.startsWith("# "))
                .map(l -> l.substring(2).strip())
                .findFirst()
                .orElse(fallback);
    }

    /**
     * The topic's text as this reader is to be shown it.
     *
     * <p>Spelled here rather than where it is printed, because a search ranks and cuts snippets
     * from the same text. A term that named the other caller's spelling would otherwise match, and
     * the snippet it matched in would hand back the operation this reader cannot carry out.
     */
    private String text(String resource) {
        return Affordance.materialize(text(loader, resource), caller);
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
