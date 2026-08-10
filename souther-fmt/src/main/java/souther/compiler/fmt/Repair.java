package souther.compiler.fmt;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The source with what the canonical form has at the units a witness names.
 *
 * <p>Composed and projected once. A witness owns no patch — two of them land on one line of the
 * canonical form often enough that this is not hypothetical — and a repair applied one at a time
 * would rewrite a line and then apply the next at an offset that line no longer has. So every
 * expectation is turned into what it says about a stretch of the source, the stretches are held
 * against each other, and the text is written once.
 *
 * <p>Every family {@link Witness} has is composed here, and the switch below is exhaustive over it
 * rather than defaulting: a rule whose expectation is added without being composed would answer with
 * a text that is not the canonical form and say nothing about having done so, and the compiler is a
 * better place to hold that than a run.
 */
final class Repair {

    private Repair() {
    }

    /** One stretch of the source, and what the canonical form has instead. */
    record Edit(int from, int to, String text) {}

    /**
     * {@code source} with the expectations of {@code witnesses} written into it.
     *
     * <p>Refuses two expectations over one stretch rather than letting the later win. Two rules
     * answering about the same characters would be a conflict the model says is not there, and
     * finding one is worth more than a text.
     */
    static String repair(String source, Formatter.CanonicalForm canonical,
            List<Witness> witnesses) {
        List<Edit> edits = new ArrayList<>();
        for (Witness w : witnesses) {
            edits.addAll(of(source, canonical, w));
        }
        edits.sort(Comparator.comparingInt(Edit::from)
                .thenComparing(Comparator.comparingInt(Edit::to).reversed()));
        StringBuilder out = new StringBuilder();
        int at = 0;
        Edit last = null;
        for (Edit e : edits) {
            if (e.equals(last)) {
                continue;   // two levels, nested one inside the other, moving the same line the
                            // same way: one expectation about it and not two
            }
            if (last != null && e.from() >= last.from() && e.to() <= last.to()) {
                // A stretch inside another's. Two rules answering about their own units whose text
                // happens to overlap -- an indent and the break that writes the line it is on -- is
                // the composition this is here to do, so it is only a conflict where the wider one
                // does not already write what the narrower asks for.
                if (last.text().endsWith(e.text())) {
                    continue;
                }
                throw new IllegalStateException(
                        "two expectations over one stretch of the source at " + e.from()
                                + ", and they do not agree: [" + last.text() + "] against ["
                                + e.text() + "]");
            }
            last = e;
            if (e.from() < at) {
                throw new IllegalStateException(
                        "two expectations over one stretch of the source, at " + e.from()
                                + "; the rules answer about their own units, and this is two of them"
                                + " answering about the same characters");
            }
            out.append(source, at, e.from()).append(e.text());
            at = e.to();
        }
        return out.append(source.substring(at)).toString();
    }

    /**
     * The stretches of the source one witness is about, in the order they are written.
     *
     * <p>Empty where what it is about is written around a comment, which the rules about comments
     * have to say before anything can be written there.
     */
    static List<Edit> of(String source, Formatter.CanonicalForm canonical, Witness w) {
        return switch (w) {
            case Witness.BetweenTwoTokens b -> List.of(spacing(source, b));
            case Witness.Separation s -> List.of(separation(source, canonical, s));
            case Witness.Indentation i -> indentation(source, canonical, i);
            case Witness.Forced f -> f.unit().adjacency() < 0
                    ? List.of(ending(source, canonical))
                    : gaps(source, canonical, List.of(f.unit().adjacency()));
            case Witness.Conditional c -> gaps(source, canonical, opportunitiesOf(canonical, c));
            case Witness.TrailingComment t -> List.of(new Edit(
                    t.unit().at() - t.source().length(), t.unit().at(), t.canonical()));
            case Witness.CommentAbove a -> List.of(under(source, a));
            case Witness.CommentCarrier c -> moved(source, canonical, c);
        };
    }

    /** Where in the source a witness lands, or -1 where nothing of it is written there. */
    static int where(String source, Formatter.CanonicalForm canonical, Witness w) {
        List<Edit> edits = of(source, canonical, w);
        return edits.isEmpty() ? -1 : edits.get(0).from();
    }

    /**
     * The columns the canonical form writes the lines of a level at.
     *
     * <p>One edit per line and one decision behind them, which is the shape the model asks for: the
     * expectation is composed over the levels and projected onto the text once. The column written
     * is the one the break was written at rather than the source's plus a step, so a level whose
     * outer level is also being moved does not have to be repaired in any order.
     *
     * <p>Every line written under the level and not only the ones written at it. A level that moves
     * takes what is nested inside it along, and those deeper levels have nothing against them —
     * their step is right and it is the column underneath that changed.
     */
    private static List<Edit> indentation(String source, Formatter.CanonicalForm canonical,
            Witness.Indentation witness) {
        Map<Newline, Integer> lines = Witnesses.sourceLines(source, canonical);
        List<Edit> out = new ArrayList<>();
        Set<Integer> at = new LinkedHashSet<>();
        for (Map.Entry<Newline, Integer> e : lines.entrySet()) {
            List<Doc.NestRef> under = e.getKey().under();
            if (!under.contains(witness.unit().inner()) || !at.add(e.getValue())) {
                continue;
            }
            int lineStart = e.getValue();
            int indent = lineStart;
            while (indent < source.length() && source.charAt(indent) == ' ') {
                indent++;
            }
            out.add(new Edit(lineStart, indent, " ".repeat(e.getKey().indent())));
        }
        return out;
    }

    /**
     * What the canonical form writes in the gaps at {@code adjacencies}.
     *
     * <p>The whole gap, since what a break rule says about one is that a line ends there and how
     * far in the next begins — the same characters the spacing rule answers for where no line ends.
     *
     * <p>A gap holding a comment on either side is left alone. Where a comment stands, what is
     * written around it is the comment rules' and copying the canonical form's text over would
     * write the comment twice or lose it.
     */
    private static List<Edit> gaps(String source, Formatter.CanonicalForm canonical,
            List<Integer> adjacencies) {
        String text = canonical.layout().text();
        List<SyntaxToken> had = Witnesses.code(CstParser.parse(source).root());
        List<SyntaxToken> writes = Witnesses.code(CstParser.parse(text).root());
        List<Edit> out = new ArrayList<>();
        for (int i : adjacencies) {
            if (i < 0 || i + 1 >= writes.size()) {
                continue;   // the file's own break, which has no token after it
            }
            String wrote = text.substring(writes.get(i).end(), writes.get(i + 1).start());
            String has = source.substring(had.get(i).end(), had.get(i + 1).start());
            if (wrote.contains("//") || has.contains("//")) {
                continue;
            }
            out.add(new Edit(had.get(i).end(), had.get(i + 1).start(), wrote));
        }
        return out;
    }

    /** Which adjacencies of the canonical form the opportunities a group settles stand at. */
    private static List<Integer> opportunitiesOf(Formatter.CanonicalForm canonical,
            Witness.Conditional witness) {
        List<SyntaxToken> writes =
                Witnesses.code(CstParser.parse(canonical.layout().text()).root());
        List<Integer> out = new ArrayList<>();
        for (Opportunity o : canonical.layout().opportunities()) {
            if (o.settledBy() != witness.unit().group()) {
                continue;
            }
            for (int i = 0; i + 1 < writes.size(); i++) {
                if (writes.get(i).end() <= o.at() && o.at() <= writes.get(i + 1).start()) {
                    out.add(i);
                    break;
                }
            }
        }
        return out;
    }

    /**
     * The lines the canonical form ends between a comment and what it is written above.
     *
     * <p>To the start of the line the next thing is on, so that how far in that line begins is left
     * where it is: that is the indentation rule's and this one has nothing to say about it.
     */
    private static Edit under(String source, Witness.CommentAbove witness) {
        int from = source.indexOf('\n', witness.unit().at());
        int to = from;
        while (to < source.length() && Character.isWhitespace(source.charAt(to))) {
            to++;
        }
        while (to > from && source.charAt(to - 1) != '\n') {
            to--;
        }
        return new Edit(from, to, "\n".repeat(witness.canonical()));
    }

    /**
     * What the canonical form writes after its last code token: the one newline a file ends with.
     *
     * <p>The file's own break stands after everything, so there is no token on the far side of it
     * and the stretch runs to the end of the text. Left to {@link #gaps}, which pairs a boundary
     * with the two tokens it stands between, this one has no pair and was written nowhere — so the
     * rule was a value, the witness was made, and neither the report nor the repair had it.
     */
    private static Edit ending(String source, Formatter.CanonicalForm canonical) {
        String text = canonical.layout().text();
        List<SyntaxToken> had = Witnesses.code(CstParser.parse(source).root());
        List<SyntaxToken> writes = Witnesses.code(CstParser.parse(text).root());
        if (had.isEmpty() || writes.isEmpty()) {
            return new Edit(source.length(), source.length(), "");
        }
        int from = had.get(had.size() - 1).end();
        int wrote = writes.get(writes.size() - 1).end();
        if (source.substring(from).contains("//") || text.substring(wrote).contains("//")) {
            return new Edit(from, from, "");   // a comment ends the file, and it is not this rule's
        }
        return new Edit(from, source.length(), text.substring(wrote));
    }

    /**
     * The two stretches a comment moves between: the one it is written in and the one it is written
     * in in the canonical form.
     *
     * <p>Both are written as the canonical form has them, which is what moves it — the comment is
     * in one of the two there and in the other here, and writing each stretch as the canonical form
     * has it leaves it in exactly one. A comment is not cut out and pasted: the stretches say what
     * they hold, and the comment is part of what they hold.
     */
    private static List<Edit> moved(String source, Formatter.CanonicalForm canonical,
            Witness.CommentCarrier witness) {
        String text = canonical.layout().text();
        List<SyntaxToken> had = Witnesses.code(CstParser.parse(source).root());
        List<SyntaxToken> writes = Witnesses.code(CstParser.parse(text).root());
        List<Edit> out = new ArrayList<>();
        for (int i : new int[] {witness.canonical(), witness.source()}) {
            if (i < 0 || i + 1 >= writes.size()) {
                continue;
            }
            out.add(new Edit(had.get(i).end(), had.get(i + 1).start(),
                    text.substring(writes.get(i).end(), writes.get(i + 1).start())));
        }
        out.sort(Comparator.comparingInt(Edit::from));
        return out;
    }

    /** What the canonical form writes between the two tokens of a boundary. */
    private static Edit spacing(String source, Witness.BetweenTwoTokens witness) {
        List<SyntaxToken> had = Witnesses.code(CstParser.parse(source).root());
        int i = witness.unit().adjacency();
        return new Edit(had.get(i).end(), had.get(i + 1).start(), witness.canonical());
    }

    /**
     * The blank lines the canonical form writes between two items.
     *
     * <p>From the end of the line the first item is written on, and not from the end of the item.
     * An item with a comment after it ends before that comment — {@link Written#end} is its last
     * code token — and a stretch beginning there would put the blank lines in front of the comment
     * and leave the ones after it where they were.
     *
     * <p>It runs to the start of the line the next thing is written on, so a comment in the gap
     * stays where it is: it belongs to the second item and is not this rule's to move.
     */
    private static Edit separation(String source, Formatter.CanonicalForm canonical,
            Witness.Separation witness) {
        List<Written> before =
                canonical.construction().places().sourcesOf(witness.unit().previous());
        int from = source.indexOf('\n', before.get(before.size() - 1).end());
        if (from < 0) {
            throw new IllegalStateException(
                    "the item before a separation ends the file, so nothing is written after it");
        }
        int to = from;
        while (to < source.length() && Character.isWhitespace(source.charAt(to))) {
            to++;
        }
        while (to > from && source.charAt(to - 1) != '\n') {
            to--;
        }
        return new Edit(from, to, "\n".repeat(witness.canonical() + 1));
    }
}
