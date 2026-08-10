package souther.compiler.fmt;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxNode;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

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

    /**
     * What the canonical form has against {@code source}. Assumes it parses.
     *
     * <p>Asked round by round, in the order the rules depend on each other. A rule that reads
     * another's result answers about a text the first has not written yet — which tokens are
     * written settles what the layout rules' boundaries are, and where the lines break settles what
     * the indentation rule's lines are — so the rules are asked, what they say is repaired, and
     * they are asked again until nothing changes.
     *
     * <p>Every round's deviations are the report's, at the place in the source they came from.
     * Keeping only the first round's would say a file has one thing wrong with it when repairing
     * that one leaves nine more.
     */
    public static Report of(String source) {
        SyntaxNode root = CstParser.parse(source).root();
        String canonical = Formatter.canonicalize(root).text();
        List<Deviation> out = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        List<List<Repair.Edit>> repaired = new ArrayList<>();
        String text = source;
        for (int round = 0; round < 8; round++) {
            Formatter.CanonicalForm form = Formatter.canonicalize(CstParser.parse(text).root());
            Witnesses.Pairing pairing = new Witnesses.Pairing(text, form);
            List<Witness> witnesses = all(text, form, pairing);
            for (Witness w : witnesses) {
                int at = Repair.where(text, form, pairing, w);
                if (at < 0) {
                    continue;
                }
                int was = at;
                for (int i = repaired.size() - 1; i >= 0; i--) {
                    was = Repair.before(repaired.get(i), was);
                }
                Deviation d = new Deviation(lineOf(source, was), columnOf(source, was), rule(w),
                        canonicalSide(w), sourceSide(w));
                if (seen.add(d.line() + ":" + d.column() + ": " + d.rule())) {
                    out.add(d);
                }
            }
            if (witnesses.isEmpty()) {
                break;
            }
            List<Repair.Edit> edits;
            try {
                edits = Repair.edits(text, form, pairing, witnesses);
            } catch (Witnesses.NoCorrespondence _) {
                return new Report(sorted(out), false);   // a family that could not answer
            }
            String next = Repair.apply(text, edits);
            if (next.equals(text)) {
                break;
            }
            repaired.add(edits);
            text = next;
        }
        return new Report(sorted(out), text.equals(canonical));
    }

    private static List<Deviation> sorted(List<Deviation> deviations) {
        List<Deviation> out = new ArrayList<>(deviations);
        out.sort(Comparator.comparingInt(Deviation::line).thenComparingInt(Deviation::column));
        return out;
    }

    /**
     * Every family's answer about one source.
     *
     * <p>A family that cannot answer is left out rather than allowed to end the report. Four of
     * them hold the two token streams side by side, and where the canonical form writes other
     * tokens than the source they have nothing to pair — so they say nothing this round, the rules
     * about which tokens are written say what they say, and the next round asks them again of a
     * source whose tokens are settled. {@link Report#whole} is what tells a reader whether that
     * ever came to the canonical form.
     *
     * <p>Only that. A family throwing anything else is a defect in the formatter or in the rule,
     * and swallowing it here would report it as this source being unusual.
     */
    private static List<Witness> all(String source, Formatter.CanonicalForm canonical) {
        return all(source, canonical, new Witnesses.Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    private static List<Witness> all(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing) {
        List<Witness> out = new ArrayList<>();
        List<Family> families = List.of(Witnesses::tokens, Witnesses::spacing,
                Witnesses::separation,
                Witnesses::indentation, Witnesses::forced, Witnesses::settled,
                Witnesses::conditional, Witnesses::comments, Witnesses::lineEnds);
        for (Family family : families) {
            try {
                out.addAll(family.of(source, canonical, pairing));
            } catch (Witnesses.NoCorrespondence _) {
                // this family has no question to ask about this source. Anything else it throws is
                // a defect and is left to be seen as one.
            }
        }
        return out;
    }

    /** What one family has against a source. */
    private interface Family {
        List<Witness> of(String source, Formatter.CanonicalForm canonical,
                Witnesses.Pairing pairing);
    }

    private static String rule(Witness w) {
        return switch (w) {
            case Witness.BetweenTwoTokens _ -> "what goes between two tokens on a line";
            case Witness.Separation _ -> Obligation.A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS.said();
            // Two statements and one rule. The step between two levels is what it says everywhere
            // inside the file; at the file itself there is no level outside to measure from, and a
            // report that told an author their definitions are one indent further in than nothing
            // would be naming a level that is not there.
            case Witness.Indentation i -> i.unit().outer() == null
                    ? "a line the file holds begins at column zero"
                    : "one level deeper is one indent further in";
            case Witness.Forced f -> f.unit().obligation().said();
            case Witness.Settled _ -> "a group written down the page ends one line where it breaks";
            case Witness.AtTheEndOfALine _ -> "a line ends where what is written on it does";
            case Witness.ACodeToken t -> t.unit().kind().said();
            case Witness.Conditional _ -> "a construct whose line would exceed the width breaks";
            case Witness.TrailingComment _ ->
                    "a comment at the end of a line is written one space after the code";
            case Witness.CommentAbove _ ->
                    "a comment on a line of its own is written above the line it owns";
            case Witness.CommentCarrier _ ->
                    "a comment is carried by the construct it was written against";
        };
    }

    private static String canonicalSide(Witness w) {
        return switch (w) {
            case Witness.BetweenTwoTokens b -> quoted(b.canonical());
            case Witness.Separation s -> lines(s.canonical());
            case Witness.Indentation i -> i.canonical() + " columns";
            case Witness.Forced f -> ends(f.canonical());
            case Witness.Settled s -> ends(s.canonical());
            case Witness.AtTheEndOfALine e -> quoted(e.canonical());
            case Witness.ACodeToken t -> quoted(t.canonical());
            case Witness.Conditional c -> c.canonicalIsWhole() ? "on one line" : "down the page";
            case Witness.TrailingComment t -> quoted(t.canonical());
            case Witness.CommentAbove a -> lineBreaks(a.canonical());
            case Witness.CommentCarrier _ -> "somewhere else";
        };
    }

    private static String sourceSide(Witness w) {
        return switch (w) {
            case Witness.BetweenTwoTokens b -> quoted(b.source());
            case Witness.Separation s -> lines(s.source());
            case Witness.Indentation i -> i.source().size() == 1
                    ? i.source().get(0) + " columns" : i.source() + " columns";
            case Witness.Forced f -> ends(f.source());
            case Witness.Settled s -> ends(s.source());
            case Witness.AtTheEndOfALine e -> quoted(e.source());
            case Witness.ACodeToken t -> quoted(t.source());
            case Witness.Conditional c -> c.sourceIsWhole() ? "on one line" : "down the page";
            case Witness.TrailingComment t -> quoted(t.source());
            case Witness.CommentAbove a -> lineBreaks(a.source());
            case Witness.CommentCarrier _ -> "here";
        };
    }

    /** How many lines end at a boundary, said as a reader would say it. */
    private static String ends(int lines) {
        return switch (lines) {
            case 0 -> "no line ends here";
            case 1 -> "one line ends here";
            case 2 -> "two do";
            default -> lines + " do";
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
