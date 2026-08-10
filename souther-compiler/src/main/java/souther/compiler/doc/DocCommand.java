package souther.compiler.doc;

import souther.compiler.check.Suggest;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * {@code souther doc}: the language specification and every doc set a bundled dependency ships,
 * answered from the CLI's own class path.
 *
 * <p>No argument lists every spec section as {@code anchor<TAB>title} followed by the shipped
 * topics as {@code set/topic<TAB>title}; a name prints that section or topic; {@code --search
 * <term>} spans both. The tab-separated listing is one line per entry so a tool — a coding agent
 * above all — can pick a name without scraping prose.
 *
 * <p>A search asks three things in turn and stops at the first that answers. Whether the term is a
 * name, which is settled rather than scored, and answers with that one document. Whether the
 * documents say it as it stands, which is a phrase search. Whether they say its words, which is
 * ranked by how many of them each document holds.
 */
public final class DocCommand {

    /** How many hits a search answers with before saying how many it held back. */
    private static final int DEFAULT_LIMIT = 20;

    private DocCommand() {}

    public static int run(String[] args, PrintStream out, PrintStream err) {
        return run(args, out, err, Caller.CLI);
    }

    static int run(String[] args, PrintStream out, PrintStream err, Caller caller) {
        return run(args, out, err, caller, DocCommand.class.getClassLoader());
    }

    static int run(String[] args, PrintStream out, PrintStream err, ClassLoader loader) {
        return run(args, out, err, Caller.CLI, loader);
    }

    static int run(String[] args, PrintStream out, PrintStream err, Caller caller, ClassLoader loader) {
        // Taken together, because the names they publish are one name space and a name resolving
        // against it is what a search asks first. Which document a name reaches is settled by the
        // two of them being held at once, not by the order this reads them.
        Documents documents = Documents.on(caller, loader);
        SpecDocument spec = documents.spec();
        LibraryDocs shipped = documents.shipped();
        if (args.length == 0) {
            for (SpecDocument.Section s : spec.sections()) {
                out.println(s.anchor() + "\t" + "  ".repeat(s.level() - 2) + s.title());
            }
            for (LibraryDocs.Topic topic : shipped.topics()) {
                out.println(topic.name() + "\t"
                        + "  ".repeat(Math.max(0, topic.depth() - 1)) + topic.title());
            }
            return 0;
        }
        if (args[0].equals("--search")) {
            if (args.length < 2 || args[1].isBlank()) {
                err.println("`--search` needs a term to look for");
                err.println("usage: souther doc --search <term> [--limit <n>]");
                return 2;
            }
            int limit = DEFAULT_LIMIT;
            for (int i = 2; i < args.length; i++) {
                if (args[i].equals("--limit") && i + 1 < args.length) {
                    try {
                        limit = Integer.parseInt(args[++i]);
                    } catch (NumberFormatException e) {
                        err.println("--limit takes a number, or 0 for everything");
                        return 2;
                    }
                }
            }
            String term = args[1];
            // What a reader arriving from a diagnostic holds is a name, and a name resolves. Asked
            // first and answered on its own, because the section a name names is not a matter of
            // how much prose says its words: a heading's anchor is written where no section's body
            // reaches, so ranking it would answer with the sections that cite it and never with it.
            SpecDocument.Section named = spec.named(term);
            if (named != null) {
                resolved(term, named.anchor(), err);
                print(named, out);
                return 0;
            }
            LibraryDocs.Topic topic = shipped.named(term);
            String shippedText = topic == null ? null : shipped.read(topic.name());
            if (shippedText != null) {
                resolved(term, topic.name(), err);
                out.print(shippedText);
                return 0;
            }
            List<String> lines = hits(spec, shipped, List.of(term), Match.ANYWHERE);
            List<String> asked = DocName.words(term);
            if (lines.isEmpty() && asked.size() > 1) {
                // Nobody's name and nobody's phrase, so what is left to answer from is the words.
                // Every section is scored against the whole query at once: taking the words one at
                // a time and laying the answers end to end would fill the page from the first of
                // them, and a reader who wrote eight words would be answered for one.
                List<String> byWord = hits(spec, shipped, asked, Match.WORD);
                if (!byWord.isEmpty()) {
                    // Said only where it happened. A term whose words are nowhere either is answered
                    // that nothing says it, and being told twice, in two ways, is being told less.
                    err.println("no section says `" + term
                            + "` — ranking the sections by how many of its words they say");
                    lines = byWord;
                }
            }
            if (lines.isEmpty()) {
                err.println("nothing says `" + term + "`");
                err.println(caller.everySectionAndTopic());
                return 0;
            }
            int shown = limit <= 0 ? lines.size() : Math.min(limit, lines.size());
            lines.subList(0, shown).forEach(out::println);
            if (shown < lines.size()) {
                out.println("… " + (lines.size() - shown) + " more; " + caller.everyHit());
            }
            return 0;
        }
        String anchor = args[0];
        if (args.length > 1) {
            err.println("`souther doc` reads one at a time; asked for "
                    + String.join(", ", List.of(args)) + " — reading `" + anchor + "`");
        }
        if (anchor.contains("/")) {
            String text = shipped.read(anchor);
            if (text == null) {
                err.println("no doc topic `" + anchor + "`");
                err.println(caller.everySectionAndTopic());
                return 2;
            }
            out.print(text);
            return 0;
        }
        SpecDocument.Section section = spec.section(anchor);
        if (section == null) {
            err.println("no section `" + anchor + "`");
            List<String> near = near(anchor, spec.names());
            if (!near.isEmpty()) {
                err.println("did you mean: " + String.join(", ", near));
            }
            err.println(caller.everySection());
            return 2;
        }
        if (!DocName.canonical(section.anchor()).equals(DocName.canonical(anchor))) {
            // A name written inside a section is answered with that section, and a reader who is
            // not told so cannot tell an answer to what they asked from the nearest thing to it.
            err.println("`" + anchor + "` is written in `" + section.anchor() + "`, which is what follows");
        }
        print(section, out);
        return 0;
    }

    /**
     * A section, headed as the document heads it.
     *
     * <p>The one place a section is written out, so that a name resolved by a search and the same
     * name read outright are answered with the same text rather than with two renderings of it.
     */
    private static void print(SpecDocument.Section section, PrintStream out) {
        out.println("=".repeat(section.level()) + " " + section.title() + " [#" + section.anchor() + "]");
        out.println();
        out.println(section.body());
    }

    /**
     * Says that {@code asked} was taken as a name, and which document it named.
     *
     * <p>A search that answers with one document rather than a list has done something the reader
     * did not ask for in so many words, and a reader who is not told cannot tell it from a search
     * that found one hit. Where the name is written inside a document rather than being that
     * document's own, that is said too: {@code an-optional-does-not-stand-in-a-boundary} is a rule
     * inside a section, and the section is what there is to answer with.
     */
    private static void resolved(String asked, String name, PrintStream err) {
        if (DocName.asWords(asked).equals(DocName.asWords(name))) {
            err.println("`" + asked + "` is a name, so it is resolved rather than searched for");
            return;
        }
        err.println("`" + asked + "` is a name written in `" + name
                + "` — resolved rather than searched for, and that is what follows");
    }

    /** What separates one part of a documentation name from the next. */
    private static final String SEGMENTS = "-/";

    /** How far a name may be from a section's and still be offered as the one that was meant. */
    private static final int NEAR_ENOUGH = 2;

    /** How many names a miss is answered with. */
    private static final int MOST_SUGGESTIONS = 5;

    /**
     * The names {@code asked} may have meant, likeliest first.
     *
     * <p>Both tests run through the same fold the lookup itself went through, so a reader who typed
     * the case the compiler prints is not told there is nothing near what they asked for.
     *
     * <p>A name that opens a section's own name is the answer on its own: {@code e1001} names the
     * diagnostic the section {@code e1001-removed} is about, and no count of edits would put the two
     * near each other. It is also what settles the question, so the spellings one keystroke away are
     * not listed beside it — {@code e1002} is a keystroke from {@code e1001} and is about something
     * else entirely.
     *
     * <p>Failing that the name is a typo, which is what an edit distance measures. Whether one name
     * occurs somewhere inside another measures neither — {@code cli} sits in the middle of
     * {@code acyclic}.
     */
    private static List<String> near(String asked, List<String> names) {
        String key = DocName.canonical(asked);
        Map<String, String> spelled = new LinkedHashMap<>();
        names.forEach(name -> spelled.putIfAbsent(DocName.canonical(name), name));

        List<String> named = spelled.entrySet().stream()
                .filter(e -> opensWith(e.getKey(), key) || opensWith(key, e.getKey()))
                .map(Map.Entry::getValue)
                .limit(MOST_SUGGESTIONS)
                .toList();
        if (!named.isEmpty()) {
            return named;
        }
        return Suggest.nearest(key, spelled.keySet(), NEAR_ENOUGH, MOST_SUGGESTIONS).stream()
                .map(spelled::get)
                .toList();
    }

    /** Whether {@code opening} is the whole of a leading run of {@code name}'s segments. */
    private static boolean opensWith(String name, String opening) {
        return name.length() > opening.length() && name.startsWith(opening)
                && SEGMENTS.indexOf(name.charAt(opening.length())) >= 0;
    }

    /**
     * What was found, best answer first, across the specification and every shipped doc set.
     *
     * <p>The two are scored the same way and sorted once. Ranking each on its own and printing one
     * after the other would put the best answer out of reach whenever the other side has enough
     * weak matches to fill the page, and the shipped topics — being few — are what would vanish.
     */
    private record Found(String name, String title, String snippet, boolean titled, int matched,
            int occurrences) {

        String rendered() {
            return name + "\t" + title + (snippet.isBlank() ? "" : "\n    " + snippet);
        }
    }

    private static List<String> hits(SpecDocument spec, LibraryDocs shipped, List<String> terms,
            Match how) {
        List<Found> found = new ArrayList<>();
        for (SpecDocument.Hit hit : spec.rank(terms, how)) {
            found.add(new Found(hit.section().anchor(), hit.section().title(), hit.snippet(),
                    hit.titled(), hit.matched(), hit.occurrences()));
        }
        for (LibraryDocs.Hit hit : shipped.rank(terms, how)) {
            found.add(new Found(hit.topic().name(), hit.topic().title(), hit.snippet(),
                    hit.titled(), hit.matched(), hit.occurrences()));
        }
        return found.stream()
                .sorted(java.util.Comparator.comparingInt(Found::matched).reversed()
                        .thenComparing(java.util.Comparator.comparing(Found::titled).reversed())
                        .thenComparing(java.util.Comparator.comparingInt(Found::occurrences).reversed()))
                .map(Found::rendered)
                .toList();
    }
}
