package souther.compiler.fmt;

import souther.compiler.cst.CstParser;

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

    /** How many times the rules are asked before a report gives up on reaching the canonical
     * form. */
    private static final int ROUNDS = 8;

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
        // The canonical form the report is held against at the end is the first round's own, and
        // each round after a repair writes the one for the text that repair produced. Asked for
        // separately, the first two are the same text written twice from the same source.
        Formatter.CanonicalForm form = Formatter.canonicalize(CstParser.parse(source).root());
        String canonical = form.text();
        List<Deviation> out = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        List<List<Repair.Edit>> repaired = new ArrayList<>();
        String text = source;
        for (int round = 0; round < ROUNDS; round++) {
            Witnesses.Pairing pairing = new Witnesses.Pairing(text, form);
            List<Witness> witnesses = all(text, form, pairing);
            if (witnesses.isEmpty()) {
                break;   // nothing to say about this text, and nothing to project it onto
            }
            // One projection for both questions this round asks of it. Where a witness lands is
            // where the first stretch it comes to begins, so a report that asked for that on its
            // own evaluated the whole projection to keep one number and then evaluated it again to
            // write the text.
            List<List<Repair.Edit>> each;
            try {
                each = Repair.each(text, form, pairing, witnesses);
            } catch (Witnesses.NoCorrespondence _) {
                return new Report(sorted(out), false);   // a family that could not answer
            }
            for (int w = 0; w < witnesses.size(); w++) {
                if (each.get(w).isEmpty()) {
                    continue;   // nothing of it is written here
                }
                int was = each.get(w).get(0).from();
                for (int i = repaired.size() - 1; i >= 0; i--) {
                    was = Repair.before(repaired.get(i), was);
                }
                Deviation d = new Deviation(lineOf(source, was), columnOf(source, was),
                        rule(witnesses.get(w)), canonicalSide(witnesses.get(w)),
                        sourceSide(witnesses.get(w)));
                if (seen.add(d.line() + ":" + d.column() + ": " + d.rule())) {
                    out.add(d);
                }
            }
            List<Repair.Edit> edits = Repair.composed(each);
            String next = Repair.apply(text, edits);
            if (next.equals(text)) {
                break;
            }
            repaired.add(edits);
            text = next;
            if (round + 1 == ROUNDS) {
                // No round is left to ask about this text. Writing its canonical form here would
                // be a pass nothing reads, and this is where the source can be one the formatter
                // refuses — so it is not written at all.
                break;
            }
            form = Formatter.canonicalize(CstParser.parse(text).root());
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
    private static List<Witness> all(String source, Formatter.CanonicalForm canonical,
            Witnesses.Pairing pairing) {
        List<Witness> out = new ArrayList<>();
        List<Family> families = List.of(Witnesses::tokens, Witnesses::spacing,
                Witnesses::separation,
                Witnesses::indentation, Witnesses::forced, Witnesses::settled,
                Witnesses::conditional, Witnesses::comments, Witnesses::lineEnds,
                Witnesses::columns);
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

    private static final String BETWEEN_TWO_TOKENS = "what goes between two tokens on a line";
    private static final String THE_FILES_OWN_LINES = "a line the file holds begins at column zero";
    private static final String ONE_LEVEL_DEEPER = "one level deeper is one indent further in";
    private static final String A_GROUPS_BREAK_ENDS_ONE_LINE =
            "a group written down the page ends one line where it breaks";
    private static final String NOTHING_AT_THE_END_OF_A_LINE =
            "a line ends where what is written on it does";
    private static final String THE_WIDTH_BREAKS =
            "a construct whose line would exceed the width breaks";
    private static final String EVERY_PLACE_IT_SETTLES =
            "a construct written down the page breaks at every place it settles";
    private static final String A_TRAILING_COMMENT =
            "a comment at the end of a line is written one space after the code";
    private static final String A_COMMENT_ABOVE =
            "a comment on a line of its own is written above the line it owns";
    private static final String A_COMMENT_IS_CARRIED =
            "a comment is carried by the construct it was written against";

    /**
     * Every rule a line of this report can name.
     *
     * <p>What the report says has to be lookupable, and a reader has nowhere to look it up unless
     * the words are written down. That makes the set of them something outside this class asks
     * about — so it is answered from the same values the report is written from, rather than from a
     * second list beside them that is right until one of the two is edited.
     */
    public static Set<String> vocabulary() {
        Set<String> out = new LinkedHashSet<>(List.of(BETWEEN_TWO_TOKENS, THE_FILES_OWN_LINES,
                ONE_LEVEL_DEEPER, A_GROUPS_BREAK_ENDS_ONE_LINE, NOTHING_AT_THE_END_OF_A_LINE,
                THE_WIDTH_BREAKS, EVERY_PLACE_IT_SETTLES, A_TRAILING_COMMENT, A_COMMENT_ABOVE,
                A_COMMENT_IS_CARRIED));
        for (Obligation o : Obligation.values()) {
            out.add(o.said());
        }
        for (Rewrites.Kind k : Rewrites.Kind.values()) {
            out.add(k.said());
        }
        for (Columns.Stop stop : Columns.Stop.values()) {
            out.add(stop.said());
        }
        return out;
    }

    private static String rule(Witness w) {
        return switch (w) {
            case Witness.BetweenTwoTokens _ -> BETWEEN_TWO_TOKENS;
            case Witness.Separation _ -> Obligation.A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS.said();
            // Two statements and one rule. The step between two levels is what it says everywhere
            // inside the file; at the file itself there is no level outside to measure from, and a
            // report that told an author their definitions are one indent further in than nothing
            // would be naming a level that is not there.
            case Witness.Indentation i -> i.unit().outer() == null
                    ? THE_FILES_OWN_LINES
                    : ONE_LEVEL_DEEPER;
            case Witness.Forced f -> f.unit().obligation().said();
            case Witness.Settled _ -> A_GROUPS_BREAK_ENDS_ONE_LINE;
            case Witness.AtTheEndOfALine _ -> NOTHING_AT_THE_END_OF_A_LINE;
            case Witness.ACodeToken t -> t.unit().kind().said();
            // Which rule decided the form is the layout's answer and not this one's. A group
            // written down the page because it holds something that cannot share a line was not
            // measured against the width, and a reader told it was would be looking for a line
            // that is not too long.
            case Witness.Conditional c -> c.why() instanceof Outcome.BrokenByForcedLayout forced
                    ? forced.obligation().said()
                    : THE_WIDTH_BREAKS;
            case Witness.RunTogether _ -> EVERY_PLACE_IT_SETTLES;
            case Witness.TrailingComment _ -> A_TRAILING_COMMENT;
            case Witness.CommentAbove _ -> A_COMMENT_ABOVE;
            case Witness.CommentCarrier _ -> A_COMMENT_IS_CARRIED;
            // One statement per stop rather than one for the rule. A reader is being told which
            // column their row missed, and the tables have different ones.
            case Witness.AtAColumn c -> c.unit().stop().said();
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
            case Witness.RunTogether r -> ends(r.canonicalBreaks() ? 1 : 0);
            case Witness.TrailingComment t -> quoted(t.canonical());
            case Witness.CommentAbove a -> lineBreaks(a.canonical());
            case Witness.CommentCarrier _ -> "somewhere else";
            case Witness.AtAColumn c -> "column " + c.canonical();
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
            case Witness.RunTogether r -> ends(r.sourceBreaks() ? 1 : 0);
            case Witness.TrailingComment t -> quoted(t.source());
            case Witness.CommentAbove a -> lineBreaks(a.source());
            case Witness.CommentCarrier _ -> "here";
            case Witness.AtAColumn c -> c.source().size() == 1
                    ? "column " + c.source().get(0) : "columns " + c.source();
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
