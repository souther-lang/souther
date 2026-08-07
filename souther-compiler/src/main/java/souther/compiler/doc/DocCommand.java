package souther.compiler.doc;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

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
        SpecDocument spec = SpecDocument.bundled();
        LibraryDocs shipped = LibraryDocs.on(loader);
        if (args.length == 0) {
            for (SpecDocument.Section s : spec.sections()) {
                out.println(s.anchor() + "\t" + "  ".repeat(s.level() - 2) + s.title());
            }
            for (LibraryDocs.Topic topic : shipped.topics()) {
                out.println(topic.name() + "\t" + topic.title());
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
            // Through the same fold the lookup itself went through: a reader who typed the case the
            // compiler prints would otherwise be told there is nothing near what they asked for.
            String asked = DocName.canonical(anchor);
            List<String> near = spec.names().stream()
                    .filter(a -> DocName.canonical(a).contains(asked)
                            || asked.contains(DocName.canonical(a)))
                    .toList();
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
