package souther.compiler.fmt;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.GreenToken;
import souther.compiler.cst.SyntaxKind;

import java.util.ArrayList;
import java.util.List;

/**
 * A declaration written out as tokens, laid out by the formatter, with the places a person still has
 * to fill in marked.
 *
 * <p>Nothing here decides what a skeleton says. What tokens to write is the caller's, and where they
 * go on the page is {@link Formatter}'s: the tokens are joined, parsed, and formatted, so a skeleton
 * is the canonical form of what it was built from and is left alone the next time the file it lands
 * in is formatted. That holds because of how it is made rather than because something checks it
 * afterwards.
 *
 * <p>The holes carry their own text — whatever a caller offers as the thing to replace — so the
 * layout is worked out over exactly the characters that will be in the buffer if they are left as
 * they stand. Nothing is padded, and no stand-in of a chosen width is needed.
 *
 * <p>Where a hole ends up is counted, not searched for. Its position among the tokens is fixed when
 * the skeleton is built, and the formatted text is held to those tokens one for one, so a hole is
 * where it was written even when its text is spelled the same as something else in the same
 * skeleton. A formatter that added, dropped or rewrote a token would break the count, and that is
 * refused rather than answered with a hole in the wrong place.
 */
public final class Skeleton {

    private Skeleton() {}

    /** Raised where the tokens do not make a declaration, or where the formatted text is not them. */
    public static final class Mismatch extends RuntimeException {
        private static final long serialVersionUID = 1L;
        Mismatch(String message) {
            super(message);
        }
    }

    /** What a hole stands for, which is what a caller has to be able to offer for it. */
    public enum Category {
        /** A name the author chooses. */
        IDENTIFIER,
        /** An expression, which nothing here can propose. */
        EXPRESSION
    }

    /** One token to write: its kind, and how it is spelled. */
    public record Word(SyntaxKind kind, String text) {}

    /** A run of tokens, either written as they are or left to be replaced. */
    public sealed interface Part {

        List<Word> words();

        /** Tokens the skeleton states. */
        record Literal(List<Word> words) implements Part {}

        /**
         * Tokens a person replaces.
         *
         * <p>A run rather than one token: what stands in for an expression may be spelled with
         * several, and a hole that could only ever be one token would have to be taken apart the
         * first time one was.
         */
        record Hole(Category category, List<Word> words) implements Part {}
    }

    /** Where a hole ended up: the stretch of the formatted text it covers. */
    public record Placed(Category category, int start, int end) {}

    /** A skeleton as it is written, and where its holes are in it. */
    public record Built(String text, List<Placed> holes) {}

    /** The token indices a hole covers, {@code from} up to but not including {@code to}. */
    record Range(Category category, int from, int to) {}

    /** {@code parts} laid out, with the holes among them placed in the result. */
    public static Built of(List<Part> parts) {
        List<Word> composed = new ArrayList<>();
        List<Range> ranges = new ArrayList<>();
        for (Part part : parts) {
            if (part.words().isEmpty()) {
                throw new Mismatch("a part of a skeleton writes no tokens");
            }
            int from = composed.size();
            composed.addAll(part.words());
            if (part instanceof Part.Hole hole) {
                ranges.add(new Range(hole.category(), from, composed.size()));
            }
        }
        // A space between every pair, which is the one join that cannot glue two tokens into a
        // third. What the source looks like here is not what comes out: the formatter derives the
        // layout from the tree, so this text is read and then thrown away.
        String source = String.join(" ", composed.stream().map(Word::text).toList());
        CstParser.Result parsed = CstParser.parse(source);
        if (!parsed.errors().isEmpty()) {
            throw new Mismatch("these tokens do not make a declaration: " + source);
        }
        String formatted = Formatter.format(parsed.root());
        return new Built(formatted, placedIn(composed, formatted, ranges));
    }

    /**
     * Where each range lands in {@code formatted}, having held it to {@code composed}.
     *
     * <p>The text is read back into tokens and matched against the ones it was built from, in order
     * and including how each is spelled. A difference anywhere means the text is not those tokens,
     * and there is then no answer to give about where a hole is in it.
     */
    static List<Placed> placedIn(List<Word> composed, String formatted, List<Range> ranges) {
        List<Placed> holes = new ArrayList<>();
        int[] starts = new int[composed.size()];
        int[] ends = new int[composed.size()];
        int seen = 0;
        int at = 0;
        for (GreenToken token : CstLexer.lex(formatted).tokens()) {
            if (token.kind().isTrivia() || token.kind() == SyntaxKind.EOF) {
                at += token.text().length();
                continue;
            }
            if (seen == composed.size()) {
                throw new Mismatch("the formatted text writes more tokens than the skeleton did");
            }
            Word word = composed.get(seen);
            if (word.kind() != token.kind() || !word.text().equals(token.text())) {
                throw new Mismatch("token " + seen + " was written as `" + word.text()
                        + "` and read back as `" + token.text() + "`");
            }
            starts[seen] = at;
            ends[seen] = at + token.text().length();
            seen++;
            at += token.text().length();
        }
        if (seen != composed.size()) {
            throw new Mismatch("the formatted text writes " + seen + " of the skeleton's "
                    + composed.size() + " tokens");
        }
        for (Range range : ranges) {
            holes.add(new Placed(range.category(), starts[range.from()], ends[range.to() - 1]));
        }
        return List.copyOf(holes);
    }
}
