package souther.compiler.fmt;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxNode;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * What the canonical form has against a source, one decision at a time.
 *
 * <p>Not the difference between two texts. A record literal written down the page moves every member
 * boundary it holds and was one decision, and a report per changed boundary tells an author how many
 * characters moved rather than what they did differently. Each of these is a rule, a place in their
 * source, and the two answers.
 *
 * <p>Where a difference is one no rule accounts for yet, {@link Report#whole} is false. A report that
 * listed what it can name and said nothing about the rest would read as a file with three things
 * wrong with it when it has five.
 */
public final class Deviations {

    private Deviations() {
    }

    /** One decision a source did not take, and where in it that shows. */
    public record Deviation(int line, int column, String rule, String canonical, String source) {}

    /**
     * What a source has against it, and whether that is all of it.
     *
     * <p>{@code whole} is what makes the list readable: it says that repairing every deviation named
     * here writes the canonical form, so a reader who acts on all of them is done.
     */
    public record Report(List<Deviation> deviations, boolean whole) {

        public Report {
            deviations = List.copyOf(deviations);
        }
    }

    /** What the canonical form has against {@code source}. Assumes it parses. */
    public static Report of(String source) {
        SyntaxNode root = CstParser.parse(source).root();
        Formatter.CanonicalForm canonical = Formatter.canonicalize(root);
        List<Witness> witnesses = all(source, canonical);
        List<Deviation> out = new ArrayList<>();
        for (Witness w : witnesses) {
            int at = Repair.where(source, canonical, w);
            if (at < 0) {
                continue;
            }
            out.add(new Deviation(lineOf(source, at), columnOf(source, at), rule(w),
                    canonicalSide(w), sourceSide(w)));
        }
        out.sort(Comparator.comparingInt(Deviation::line).thenComparingInt(Deviation::column));
        return new Report(out, settles(source, canonical.text()));
    }

    /** Every family's answer about one source. */
    private static List<Witness> all(String source, Formatter.CanonicalForm canonical) {
        List<Witness> out = new ArrayList<>(Witnesses.spacing(source, canonical));
        out.addAll(Witnesses.separation(source, canonical));
        out.addAll(Witnesses.indentation(source, canonical));
        out.addAll(Witnesses.forced(source, canonical));
        out.addAll(Witnesses.conditional(source, canonical));
        out.addAll(Witnesses.comments(source, canonical));
        return out;
    }

    /**
     * Whether repairing what the rules say writes the canonical form.
     *
     * <p>Applied until it stops changing the text. A rule that reads another's result answers about
     * lines the first has not written yet, so one pass says less than the rules do together.
     */
    private static boolean settles(String source, String canonical) {
        String text = source;
        for (int round = 0; round < 8; round++) {
            Formatter.CanonicalForm form = Formatter.canonicalize(CstParser.parse(text).root());
            List<Witness> witnesses = all(text, form);
            if (witnesses.isEmpty()) {
                break;
            }
            String next = Repair.repair(text, form, witnesses);
            if (next.equals(text)) {
                break;
            }
            text = next;
        }
        return text.equals(canonical);
    }

    private static String rule(Witness w) {
        return switch (w) {
            case Witness.BetweenTwoTokens _ -> "what goes between two tokens on a line";
            case Witness.Separation _ -> Obligation.A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS.said();
            case Witness.Indentation _ -> "one level deeper is one indent further in";
            case Witness.Forced f -> f.unit().obligation().said();
            case Witness.Conditional _ -> "a construct whose line would exceed the width breaks";
            case Witness.TrailingComment _ ->
                    "a comment at the end of a line is written one space after the code";
            case Witness.CommentAbove _ ->
                    "a comment on a line of its own is written above the line it owns";
        };
    }

    private static String canonicalSide(Witness w) {
        return switch (w) {
            case Witness.BetweenTwoTokens b -> quoted(b.canonical());
            case Witness.Separation s -> lines(s.canonical());
            case Witness.Indentation i -> i.canonical() + " columns";
            case Witness.Forced _ -> "a line ends here";
            case Witness.Conditional c -> c.canonicalIsWhole() ? "on one line" : "down the page";
            case Witness.TrailingComment t -> quoted(t.canonical());
            case Witness.CommentAbove a -> lineBreaks(a.canonical());
        };
    }

    private static String sourceSide(Witness w) {
        return switch (w) {
            case Witness.BetweenTwoTokens b -> quoted(b.source());
            case Witness.Separation s -> lines(s.source());
            case Witness.Indentation i -> i.source().size() == 1
                    ? i.source().get(0) + " columns" : i.source() + " columns";
            case Witness.Forced _ -> "it does not";
            case Witness.Conditional c -> c.sourceIsWhole() ? "on one line" : "down the page";
            case Witness.TrailingComment t -> quoted(t.source());
            case Witness.CommentAbove a -> lineBreaks(a.source());
        };
    }

    private static String lineBreaks(int lines) {
        return lines == 1 ? "the next line" : lines - 1 + " blank lines before the next";
    }

    private static String lines(int blank) {
        return blank == 1 ? "one blank line" : blank + " blank lines";
    }

    private static String quoted(String text) {
        return text.isEmpty() ? "nothing"
                : "`" + text.replace("\n", "\\n").replace("\t", "\\t") + "`";
    }

    private static int lineOf(String source, int at) {
        int line = 1;
        for (int i = 0; i < at && i < source.length(); i++) {
            if (source.charAt(i) == '\n') {
                line++;
            }
        }
        return line;
    }

    private static int columnOf(String source, int at) {
        return at - (source.lastIndexOf('\n', Math.max(0, at - 1)) + 1) + 1;
    }
}
