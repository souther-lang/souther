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
        SpecDocument spec = SpecDocument.bundled(caller);
        LibraryDocs shipped = LibraryDocs.on(loader, caller);
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
                if (!args[i].equals("--limit")) {
                    continue;
                }
                // Written last, this used to fall out of the condition and leave the default in
                // force — the search ran, answered under a limit nobody asked for, and said nothing
                // about the option it dropped. A caller reaching this command through `souther doc`
                // is refused before it; one reaching it directly is refused here.
                if (i + 1 >= args.length) {
                    err.println("--limit takes a number, or 0 for everything");
                    return 2;
                }
                try {
                    limit = Integer.parseInt(args[++i]);
                } catch (NumberFormatException e) {
                    err.println("--limit takes a number, or 0 for everything");
                    return 2;
                }
            }
            String term = args[1];
            List<String> lines = new ArrayList<>(hits(spec, shipped, term));
            if (lines.isEmpty() && term.contains(" ")) {
                // A phrase is matched whole, so a reader who typed a question rather than a term
                // gets nothing. Rather than answer with silence, the words are tried separately.
                err.println("no section says `" + term + "` — searching for its words instead");
                for (String word : term.split("\\s+")) {
                    for (String line : hits(spec, shipped, word)) {
                        if (!lines.contains(line)) {
                            lines.add(line);
                        }
                    }
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
        out.println("=".repeat(section.level()) + " " + section.title() + " [#" + section.anchor() + "]");
        out.println();
        out.println(section.body());
        return 0;
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
    private record Found(String name, String title, String snippet, boolean titled, int occurrences) {

        String rendered() {
            return name + "\t" + title + (snippet.isBlank() ? "" : "\n    " + snippet);
        }
    }

    private static List<String> hits(SpecDocument spec, LibraryDocs shipped, String term) {
        List<Found> found = new ArrayList<>();
        for (SpecDocument.Hit hit : spec.rank(term)) {
            found.add(new Found(hit.section().anchor(), hit.section().title(), hit.snippet(),
                    hit.titled(), hit.occurrences()));
        }
        for (LibraryDocs.Hit hit : shipped.rank(term)) {
            found.add(new Found(hit.topic().name(), hit.topic().title(), hit.snippet(),
                    hit.titled(), hit.occurrences()));
        }
        return found.stream()
                .sorted(java.util.Comparator.comparing(Found::titled).reversed()
                        .thenComparing(java.util.Comparator.comparingInt(Found::occurrences).reversed()))
                .map(Found::rendered)
                .toList();
    }
}
