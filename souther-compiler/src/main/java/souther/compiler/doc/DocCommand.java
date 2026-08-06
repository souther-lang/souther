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
        return run(args, out, err, DocCommand.class.getClassLoader());
    }

    static int run(String[] args, PrintStream out, PrintStream err, ClassLoader loader) {
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
            if (args.length < 2) {
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
            List<String> lines = hits(spec, shipped, term);
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
                err.println("`souther doc` lists every section and topic");
                return 0;
            }
            int shown = limit <= 0 ? lines.size() : Math.min(limit, lines.size());
            lines.subList(0, shown).forEach(out::println);
            if (shown < lines.size()) {
                out.println("… " + (lines.size() - shown) + " more; `--limit 0` for all of them");
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
                err.println("`souther doc` lists every section and topic");
                return 2;
            }
            out.print(text);
            return 0;
        }
        SpecDocument.Section section = spec.section(anchor);
        if (section == null) {
            err.println("no section `" + anchor + "`");
            List<String> near = spec.sections().stream()
                    .map(SpecDocument.Section::anchor)
                    .filter(a -> a.contains(anchor) || anchor.contains(a))
                    .toList();
            if (!near.isEmpty()) {
                err.println("did you mean: " + String.join(", ", near));
            }
            err.println("`souther doc` lists every section");
            return 2;
        }
        out.println("=".repeat(section.level()) + " " + section.title() + " [#" + section.anchor() + "]");
        out.println();
        out.println(section.body());
        return 0;
    }

    /** One hit per entry: the tab-separated name and title, and under it the line it matched on. */
    private static List<String> hits(SpecDocument spec, LibraryDocs shipped, String term) {
        List<String> lines = new ArrayList<>();
        for (SpecDocument.Hit hit : spec.rank(term)) {
            lines.add(hit.section().anchor() + "\t" + hit.section().title()
                    + (hit.snippet().isBlank() ? "" : "\n    " + hit.snippet()));
        }
        for (LibraryDocs.Topic topic : shipped.search(term)) {
            String snippet = shipped.snippet(topic, term);
            lines.add(topic.name() + "\t" + topic.title()
                    + (snippet.isBlank() ? "" : "\n    " + snippet));
        }
        return lines;
    }
}
