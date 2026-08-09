package souther.compiler.fmt;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

/**
 * The source with what the canonical form has at the units a witness names.
 *
 * <p>Composed and projected once. A witness owns no patch — two of them land on one line of the
 * canonical form often enough that this is not hypothetical — and a repair applied one at a time
 * would rewrite a line and then apply the next at an offset that line no longer has. So every
 * expectation is turned into what it says about a stretch of the source, the stretches are held
 * against each other, and the text is written once.
 *
 * <p>Two families so far: the ones whose expectation is a stretch of text. What the others need is
 * not more machinery here but their expectations said the same way.
 */
final class Repair {

    private Repair() {
    }

    /** One stretch of the source, and what the canonical form has instead. */
    private record Edit(int from, int to, String text) {}

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
            switch (w) {
                case Witness.BetweenTwoTokens b -> edits.add(spacing(source, b));
                case Witness.Separation s -> edits.add(separation(source, canonical, s));
                default -> throw new IllegalArgumentException(
                        "no expectation is composed for " + w.getClass().getSimpleName()
                                + " yet, and a repair that skipped it would answer with a text that"
                                + " is not the canonical form");
            }
        }
        edits.sort(Comparator.comparingInt(Edit::from));
        StringBuilder out = new StringBuilder();
        int at = 0;
        for (Edit e : edits) {
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
