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
import java.util.Locale;
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
     * <p>{@code from} and {@code to} are what is read: the whole file for a document, and for a
     * named part, its heading through to the next heading that closes it. A part carries its
     * subordinate parts the way a specification section carries its subsections, so asking for the
     * larger thing is asking for all of it.
     *
     * <p>{@code own} is what is searched: this one's extent with the extent of every part named
     * inside it taken out. Reading and searching want different things from the same text — a
     * reader asking for the larger thing wants all of it, and a search that ranked the larger thing
     * over all of it would answer one occurrence twice, once as the part it is written in and once
     * as everything containing that part.
     *
     * <p>It is a list because what is left is not one run. A part ends at the next heading beside
     * it, named or not, so an unnamed heading inside a part closes the named part before it and the
     * text under it goes on belonging to the part around them both. Written as one range ending
     * where the first named part inside begins, that text would belong to nobody and a search would
     * not find it. Every character of a file belongs to exactly one of these, which is what makes
     * finding it once and finding it at all the same guarantee.
     *
     * <p>{@code depth} is 0 for a document and the heading's level for a part of one, which is what
     * a listing indents by.
     */
    public record Topic(String name, String title, int depth, String resource, int from, int to,
            List<Slice> own) {}

    /** A run of a file, from one position up to another. */
    public record Slice(int from, int to) {}

    private final ClassLoader loader;
    /** Keyed by {@link DocName#canonical}, so a topic is found in whatever case it is asked for.
     *  The topic keeps its own spelling: the name is also the path its text is read from. */
    private final Map<String, Topic> byName;
    /** The same topics keyed by {@link DocName#asWords}, which is how a search resolves a name.
     *  The same topics: a name that reaches one of these reaches the other. */
    private final Map<String, Topic> byWords;
    /**
     * What a search ranks: every file and every part of one, each over its own text.
     *
     * <p>The own texts of a file and its parts divide that file between them, so a term written
     * once is answered once, by the smallest thing that has it, and a term written anywhere is
     * answered by something.
     */
    private final List<Topic> ranked;
    /** Who the text is spelled for, wherever it sends its reader somewhere. */
    private final Caller caller;

    private LibraryDocs(ClassLoader loader, Map<String, Topic> byName, Map<String, Topic> byWords,
            List<Topic> ranked, Caller caller) {
        this.loader = loader;
        this.byName = byName;
        this.byWords = byWords;
        this.ranked = ranked;
        this.caller = caller;
    }

    /** The doc sets reachable through {@code loader} — for the CLI, everything bundled with it. */
    public static LibraryDocs on(ClassLoader loader) {
        return on(loader, Caller.CLI);
    }

    /** The same sets, read as {@code caller} is to be answered. */
    static LibraryDocs on(ClassLoader loader, Caller caller) {
        Names named = new Names();
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
                        String file = entry.strip();
                        String topic = set + "/" + file.replaceFirst("\\.md$", "");
                        String resource = ROOT + set + "/" + file;
                        String text = Affordance.materialize(text(loader, resource), caller);
                        List<Named> parts = named(topic, text);
                        // The file, and then each part it names. What is searched of each is its
                        // extent with the parts named inside it taken out, so the file and its parts
                        // divide it between them: nothing is counted twice and nothing is left out.
                        Topic whole = new Topic(topic, titleOf(text, file), 0, resource, 0,
                                text.length(), without(0, text.length(), parts));
                        named.register(whole);
                        ranked.add(whole);
                        for (Named part : parts) {
                            Topic held = new Topic(part.name(), part.title(), part.level(), resource,
                                    part.from(), part.to(),
                                    without(part.from(), part.to(), inside(part, parts)));
                            named.register(held);
                            ranked.add(held);
                        }
                    }
                }
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return new LibraryDocs(loader, named.byName, named.byWords, List.copyOf(ranked), caller);
    }

    /**
     * The topics read so far, under each fold a lookup uses.
     *
     * <p>A topic is registered under both or under neither. A doc set naming two topics that come
     * together under either fold has published one name for two documents, and which of them a
     * reader is answered with would be settled by the order its registry happened to list them —
     * the read path taking the last and a search taking the first. That the names are a jar's to
     * choose is why it is refused where the jar is read rather than settled quietly here.
     */
    private static final class Names {

        private final Map<String, Topic> byName = new LinkedHashMap<>();
        private final Map<String, Topic> byWords = new LinkedHashMap<>();
        private final Map<String, String> askedAs = new LinkedHashMap<>();

        void register(Topic topic) {
            Topic taken = byName.put(DocName.canonical(topic.name()), topic);
            if (taken != null) {
                throw new IllegalStateException("two shipped topics are asked for by the same name: `"
                        + taken.name() + "` and `" + topic.name() + "`");
            }
            String words = DocName.asWords(topic.name());
            String said = askedAs.put(words, topic.name());
            if (said != null) {
                throw new IllegalStateException("two shipped topics are the same words: `"
                        + said + "` and `" + topic.name() + "`");
            }
            byWords.put(words, topic);
        }
    }

    /** A part a file named: where its declaration is, and what is read of it. */
    private record Named(String name, String title, int level, int declaredAt, int from, int to) {}

    /**
     * The parts {@code text} names of itself, each running to the heading that closes it.
     *
     * <p>A declaration that opens nothing is a mistake in the doc set rather than a part with no
     * text: the name would be published, answered with whatever followed it, and moved the next
     * time the file was edited. It is refused where the set is read.
     */
    private static List<Named> named(String topic, String text) {
        // Every heading, whether the file names it or not: what closes a part is the next heading
        // that is not under it, and a heading the set chose not to name still is not under it.
        // What a block taken as it stands says is what it shows a reader — a `## Example input` in
        // a fenced sample neither opens a section nor closes one, and a declaration written in one
        // is what the sample looks like rather than a name to publish.
        record Head(String name, String title, int level, int declaredAt, int from) {}
        List<Head> heads = new ArrayList<>();
        String[] lines = text.split("\n", -1);
        boolean[] opaque = TakenAsItStands.markdown(lines);
        int[] starts = new int[lines.length];
        for (int i = 0, at = 0; i < lines.length; i++) {
            starts[i] = at;
            at += lines[i].length() + 1;
        }
        for (int i = 0; i < lines.length; i++) {
            if (opaque[i]) {
                continue;
            }
            Matcher declaration = DECLARED.matcher(lines[i]);
            if (declaration.matches()) {
                Matcher heading = i + 1 < lines.length && !opaque[i + 1]
                        ? HEADING.matcher(lines[i + 1]) : null;
                if (heading == null || !heading.matches()) {
                    throw new IllegalStateException("`" + topic + "` names a section `"
                            + declaration.group(1) + "` above something that is not a heading");
                }
                heads.add(new Head(topic + "/" + declaration.group(1), heading.group(2),
                        heading.group(1).length(), starts[i], starts[i + 1]));
                i++;
                continue;
            }
            Matcher heading = HEADING.matcher(lines[i]);
            if (heading.matches()) {
                heads.add(new Head(null, heading.group(2), heading.group(1).length(),
                        starts[i], starts[i]));
            }
        }
        List<Named> parts = new ArrayList<>();
        for (int h = 0; h < heads.size(); h++) {
            Head here = heads.get(h);
            if (here.name() == null) {
                continue;
            }
            int to = text.length();
            for (int n = h + 1; n < heads.size(); n++) {
                if (heads.get(n).level() <= here.level()) {
                    to = heads.get(n).declaredAt();
                    break;
                }
            }
            // A part is read from its heading, not from the line naming it. That line is the
            // heading's, the way an anchor above a specification heading is, so it ends the part
            // before it rather than opening this one.
            parts.add(new Named(here.name(), here.title(), here.level(), here.declaredAt(),
                    here.from(), to));
        }
        return parts;
    }

    /** The parts named inside {@code held}, which are the ones its own text does not carry. */
    private static List<Named> inside(Named held, List<Named> parts) {
        return parts.stream()
                .filter(part -> part.declaredAt() > held.declaredAt() && part.to() <= held.to())
                .toList();
    }

    /**
     * {@code from} to {@code to}, with each of {@code taken} left out of it.
     *
     * <p>What is left is a list rather than a range because a part need not end where the one
     * named inside it does: an unnamed heading closes the named part before it, and the text under
     * that heading goes on belonging to the part around them both. A range ending at the first
     * name inside would leave that text to nobody.
     */
    private static List<Slice> without(int from, int to, List<Named> taken) {
        List<Slice> left = new ArrayList<>();
        int at = from;
        for (Named part : taken) {
            if (part.declaredAt() >= to) {
                break;
            }
            if (part.declaredAt() > at) {
                left.add(new Slice(at, part.declaredAt()));
            }
            at = Math.max(at, part.to());
        }
        if (at < to) {
            left.add(new Slice(at, to));
        }
        return List.copyOf(left);
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

    /**
     * The topic {@code query} is the name of, written as its words or as its doc set spells it, or
     * null when it names nothing. The same question {@link #read} answers, asked the way a reader
     * who has the name says it aloud.
     */
    public Topic named(String query) {
        return DocName.isName(query) ? byWords.get(DocName.asWords(query)) : null;
    }

    /** Every topic whose title or text contains {@code term}, case-insensitively. */
    public List<Topic> search(String term) {
        return rank(term).stream().map(Hit::topic).toList();
    }

    /** A topic the query was found in, scored the same way a specification section is. */
    public record Hit(Topic topic, boolean titled, int matched, int occurrences, String snippet) {}

    /**
     * The topics that say {@code term} as it stands, each with what a caller needs to rank it
     * against a specification section.
     */
    public List<Hit> rank(String term) {
        if (term == null || term.isBlank()) {
            return List.of();
        }
        return rank(List.of(term), Match.ANYWHERE);
    }

    /**
     * The topics that say any of {@code terms}: how much of the query each holds, whether its title
     * or its name is what was asked for, how often it is said, and the line one was found on.
     *
     * <p>Scored the way a specification section is, by the same {@link Match}, because the two are
     * merged into one answer and sorted once. A shipped topic ranked under its own meaning of the
     * numbers beside it would be placed against sections it was never compared with.
     */
    List<Hit> rank(List<String> asked, Match how) {
        List<String> terms = asked.stream().map(DocName::canonical).toList();
        List<Hit> hits = new ArrayList<>();
        for (Topic topic : ranked) {
            Match.Held held = how.held(
                    (topic.title() + " " + topic.name()).toLowerCase(Locale.ROOT),
                    own(topic).toLowerCase(Locale.ROOT), terms);
            if (held.matched() > 0) {
                hits.add(new Hit(topic, held.named(), held.matched(), held.occurrences(),
                        snippet(topic, terms, how)));
            }
        }
        return hits;
    }

    /** The line of {@code topic} that says {@code term}, cut to a readable width. */
    public String snippet(Topic topic, String term) {
        return snippet(topic, List.of(DocName.canonical(term)), Match.ANYWHERE);
    }

    /** The line of {@code topic} that says one of {@code terms}, cut to a readable width. */
    private String snippet(Topic topic, List<String> terms, Match how) {
        String line = own(topic).lines()
                .map(String::strip)
                .filter(l -> !l.isEmpty() && !l.startsWith("#") && !l.startsWith("|"))
                .filter(l -> terms.stream()
                        .anyMatch(term -> how.says(l.toLowerCase(Locale.ROOT), term)))
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
        String text = whole(topic);
        return topic.from() == 0 && topic.to() >= text.length()
                ? text : text.substring(topic.from(), Math.min(topic.to(), text.length()));
    }

    /** The text this topic is searched over: its own, with what it names inside it left to that. */
    private String own(Topic topic) {
        String text = whole(topic);
        StringBuilder held = new StringBuilder();
        for (Slice slice : topic.own()) {
            held.append(text, Math.min(slice.from(), text.length()),
                    Math.min(slice.to(), text.length()));
        }
        return held.toString();
    }

    private String whole(Topic topic) {
        return Affordance.materialize(text(loader, topic.resource()), caller);
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
