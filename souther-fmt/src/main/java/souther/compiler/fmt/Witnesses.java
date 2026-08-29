package souther.compiler.fmt;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a canonical form has against the source it was made from.
 *
 * <p>Not a diff. The text differs at every boundary a decision moved, and a rule answers about its
 * own unit — so this attributes the differences to the units they came from and hands back one
 * witness per unit, which is what an author can act on.
 *
 * <p>One family per rule, and each of them answers about its own unit: a boundary for spacing, a pair
 * of items for separation, a pair of levels for indentation, a group for conditional layout, a
 * comment for the rules about comments, a site of the source for the rules about which code tokens
 * are written, a column of a table for the rule that lines its rows up.
 *
 * <p>A family reads the results of the rules it depends on rather than competing with them, and
 * where what it depends on is not settled yet it says nothing: the rules are asked again once it is.
 */
final class Witnesses {

    private Witnesses() {
    }

    /**
     * A source and its canonical form that cannot be held against each other, so a rule that asks
     * what the source has at a unit of the canonical form has no question to ask.
     *
     * <p>A kind of its own, and not the exception a broken invariant throws. What a family says by
     * throwing this is that it cannot answer about this source — which is a fact about the source
     * and one a report can carry — and what it says by throwing anything else is that something
     * here is wrong. A caller that treated the two alike would take a defect for an incompleteness
     * and say the report is merely not whole.
     */
    static final class NoCorrespondence extends RuntimeException {

        private static final long serialVersionUID = 1L;

        NoCorrespondence(String said) {
            super(said);
        }
    }

    /**
     * What the rules about which code tokens are written have against {@code source}.
     *
     * <p>Read from the source alone. Where the two texts' tokens differ, no rule that pairs them
     * can be asked at all, so this one is asked first and of the source's own tree: the sites are
     * the ones the grammar admits, and what the canonical form writes at each of them is the rule.
     */
    static List<Witness> tokens(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        return tokens(source, canonical);
    }

    /** What the rules about which code tokens are written have against {@code source}. */
    static List<Witness> tokens(String source, Formatter.CanonicalForm canonical) {
        List<Witness> out = new ArrayList<>();
        for (Rewrites.Site site : Rewrites.sitesOf(CstParser.parse(source).root())) {
            out.add(new Witness.ACodeToken(new Witness.TokenSite(site.kind(), site.from()),
                    site.canonical(), site.source()));
        }
        return out;
    }

    /**
     * What the indentation rule has against {@code source}.
     *
     * <p>A level's column on each side. The canonical form's is what the layout wrote; the source's
     * is the column it put the same element in, found through the correspondence rather than by
     * counting lines in step — the two texts do not have the same lines, which is the point.
     *
     * <p>A level the source did not begin a line for is not answered here. What happened there is
     * that the source did not break where the canonical form does, which is the conditional or
     * forced layout rule's to report; asking this rule about it would have it name an indent for a
     * line nobody wrote.
     */
    static List<Witness> indentation(String source, Formatter.CanonicalForm canonical) {
        return indentation(source, canonical, new Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    static List<Witness> indentation(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        Map<Doc.NestRef, Integer> written = new IdentityHashMap<>();
        Map<Doc.NestRef, Set<Integer>> had = new IdentityHashMap<>();

        List<CanonicalLine> lines = lines(source, canonical, pairing);
        for (CanonicalLine line : lines) {
            Doc.NestRef innermost = line.under().get(line.under().size() - 1);
            Integer already = written.put(innermost, line.indent());
            if (already != null && already != line.indent()) {
                throw new IllegalStateException(
                        "one level of nesting, written at column " + already + " and at column "
                                + line.indent() + "; a level has one column and the layout wrote"
                                + " two");
            }
            if (line.sourceStart() != null) {
                had.computeIfAbsent(innermost, _ -> new LinkedHashSet<>())
                        .add(indentAt(source, line.sourceStart()));
            }
        }

        List<Witness> out = new ArrayList<>();
        Set<Witness.Levels> seen = new LinkedHashSet<>();
        for (CanonicalLine line : lines) {
            for (int i = 0; i < line.under().size(); i++) {
                Doc.NestRef inner = line.under().get(i);
                Doc.NestRef outer = i == 0 ? null : line.under().get(i - 1);
                Witness.Levels unit = new Witness.Levels(outer, inner);
                if (!seen.add(unit)) {
                    continue;
                }
                Integer step = step(written, outer, inner);
                List<Integer> wrote = sourceSteps(had, outer, inner);
                if (step != null && wrote != null && !wrote.equals(List.of(step))) {
                    out.add(new Witness.Indentation(unit, step, wrote));
                }
            }
        }
        return out;
    }

    /**
     * A line the canonical form writes: how far in it begins, the levels it is written under, and
     * where the source begins the same line.
     *
     * <p>{@code sourceStart} is the offset that line starts at in the source, so that what stands in
     * front of the first thing on it is the indent a repair writes over, and null where the source
     * opened no line there — it broke somewhere else, and moving an indent would be answering a
     * question about a line nobody wrote.
     */
    record CanonicalLine(int indent, List<Doc.NestRef> under, Integer sourceStart) {

        CanonicalLine {
            under = List.copyOf(under);
        }
    }

    /**
     * The lines the canonical form writes, in the order it writes them.
     *
     * <p>One per break, and the one the file opens with: nothing breaks in front of the first line,
     * and left out of this the column it begins at is a column no rule was ever asked about.
     *
     * <p>A break leaving a blank line is not one of these. Its line has nothing on it, so it is at
     * no level's column and a reader taking its zero for one would have the level it stands under
     * written at two columns.
     */
    static List<CanonicalLine> lines(String source, Formatter.CanonicalForm canonical) {
        return lines(source, canonical, new Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    static List<CanonicalLine> lines(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        Layout layout = canonical.layout();
        Map<Integer, Place> opened = placesByStart(layout);
        List<CanonicalLine> out = new ArrayList<>();
        List<Doc.NestRef> file = fileLevel(layout);
        if (!file.isEmpty()) {
            out.add(new CanonicalLine(indentAt(layout.text(), 0), file, 0));
        }
        for (Newline n : layout.breaks()) {
            if (n.under().isEmpty() || !n.indents()) {
                continue;
            }
            out.add(new CanonicalLine(n.indent(), n.under(),
                    lineStartFor(source, canonical, opened, pairing, n)));
        }
        return out;
    }

    /**
     * The two texts' tokens, read once for a whole run of questions about their lines.
     *
     * <p>The comments are here as well as the code. A line the canonical form opens for a comment is
     * one no place is written at, and asked through the code alone it comes back as the line of the
     * next token — a line the comment is not on. That is what left a comment written anywhere at all
     * with no rule to answer for its column.
     */
    static final class Pairing {

        private final Run hadCode;
        private final Run writesCode;
        private final List<SyntaxToken> hadComments;
        private final List<SyntaxToken> writesComments;
        private final Map<Integer, Integer> writesCommentAt;

        Pairing(String source, Formatter.CanonicalForm canonical) {
            this(source, canonical.layout().text());
        }

        Pairing(String source, String text) {
            this(CstParser.parse(source).root(), CstParser.parse(text).root());
        }

        private Pairing(SyntaxNode source, SyntaxNode text) {
            this(code(source), code(text), comments(source), comments(text));
        }

        Pairing(List<SyntaxToken> hadCode, List<SyntaxToken> writesCode,
                List<SyntaxToken> hadComments, List<SyntaxToken> writesComments) {
            this.hadCode = new Run(hadCode);
            this.writesCode = new Run(writesCode);
            this.hadComments = List.copyOf(hadComments);
            this.writesComments = List.copyOf(writesComments);
            Map<Integer, Integer> at = new LinkedHashMap<>();
            for (int i = 0; i < this.writesComments.size(); i++) {
                at.putIfAbsent(this.writesComments.get(i).start(), i);
            }
            this.writesCommentAt = at;
        }

        List<SyntaxToken> hadCode() {
            return hadCode.tokens();
        }

        List<SyntaxToken> writesCode() {
            return writesCode.tokens();
        }

        List<SyntaxToken> hadComments() {
            return hadComments;
        }

        List<SyntaxToken> writesComments() {
            return writesComments;
        }

        /**
         * Which adjacency of the canonical form's tokens {@code at} stands in, or -1 where it
         * stands in none of them.
         *
         * <p>Every question about a place of the canonical form is asked at an offset of it — a
         * break's, an opportunity's — and answered at the adjacency the offset stands in. The
         * canonical form's run is the one they are asked of, because it is the one that has the
         * places; what the source has at the same adjacency is then read from its own tokens.
         */
        int adjacencyAt(int at) {
            return writesCode.adjacencyAt(at);
        }

        /** Which of the canonical form's code tokens stands in front of {@code at}, or -1 where
         *  none does. */
        int writesInFrontOf(int at) {
            return writesCode.inFrontOf(at);
        }

        /** Which of the source's code tokens stands in front of {@code at}, or -1 where none
         *  does. */
        int hadInFrontOf(int at) {
            return hadCode.inFrontOf(at);
        }

        /** Which comment the canonical form writes at {@code start}, or null where it writes none
         *  there. */
        Integer commentWrittenAt(int start) {
            return writesCommentAt.get(start);
        }
    }

    /**
     * A run of code tokens, with where an offset stands among them searched for rather than walked
     * to.
     *
     * <p>The families ask the same two questions of the same two runs, once for every place they
     * answer about: which adjacency an offset stands in, and which token stands in front of it.
     * Asked by walking the run, each answer costs its length, and the places are as many as the
     * tokens — so a report over a file cost the square of it.
     *
     * <p>A run is written in order and its tokens do not overlap, so both of a token's ends rise
     * along it and either question is a search on a sorted list. What is held beside the tokens is
     * two runs of {@code int} the length of the run — where each token starts, and where it ends —
     * so that a search reads numbers laid out together rather than following a token at every step.
     *
     * <p>Searched and not tabulated by offset. A table indexed by character would answer in one
     * step, and it would be the length of the text rather than of the run: a source is not made of
     * tokens at an even rate, and one holding a long literal or a page of comments above its first
     * declaration would carry a table many times the size of everything else about it — for a
     * question asked at a few thousand offsets.
     *
     * <p>Two searches and not one, because the two questions are not the same question. An offset
     * inside a token stands in no adjacency and still has a token in front of it, and an offset
     * past the last token has a token in front of it and no adjacency after it.
     */
    static final class Run {

        private final List<SyntaxToken> tokens;

        /** Where each token starts, rising along the run. */
        private final int[] starts;

        /** Where each token ends, rising along the run. */
        private final int[] ends;

        Run(List<SyntaxToken> tokens) {
            this.tokens = List.copyOf(tokens);
            this.starts = new int[this.tokens.size()];
            this.ends = new int[this.tokens.size()];
            for (int i = 0; i < this.tokens.size(); i++) {
                this.starts[i] = this.tokens.get(i).start();
                this.ends[i] = this.tokens.get(i).end();
            }
        }

        List<SyntaxToken> tokens() {
            return tokens;
        }

        /**
         * Which adjacency {@code at} stands in, or -1 where it stands in none.
         *
         * <p>The first of them, which is what the walk this replaced returned. An adjacency holds
         * {@code at} where the token before it has ended and the token after it has not begun; the
         * first is a prefix of the run and the second a suffix, so the ones that hold it are a
         * stretch and the answer is where that stretch begins.
         *
         * <p>Past the last token there is no adjacency: the run has one fewer than it has tokens,
         * and an offset after the last of them is inside none of them.
         */
        int adjacencyAt(int at) {
            int ended = inFrontOf(at);
            if (ended < 0) {
                return -1;
            }
            int first = Math.max(firstStartingAt(at) - 1, 0);
            return first <= Math.min(ended, tokens.size() - 2) ? first : -1;
        }

        /** The first token that begins at or after {@code at}, or the length of the run. */
        private int firstStartingAt(int at) {
            int low = 0;
            int high = starts.length;
            while (low < high) {
                int mid = (low + high) >>> 1;
                if (starts[mid] < at) {
                    low = mid + 1;
                } else {
                    high = mid;
                }
            }
            return low;
        }

        /**
         * Which token stands in front of {@code at}, or -1 where none does: the last one to have
         * ended by it.
         */
        int inFrontOf(int at) {
            int low = 0;
            int high = ends.length - 1;
            int found = -1;
            while (low <= high) {
                int mid = (low + high) >>> 1;
                if (ends[mid] <= at) {
                    found = mid;
                    low = mid + 1;
                } else {
                    high = mid - 1;
                }
            }
            return found;
        }
    }

    /**
     * The levels the file's own first line is written under: the outermost one alone.
     *
     * <p>Read from a break rather than named, because which nesting the file is is the document's
     * to say. Every break is written inside it, so the first of any break's levels is it.
     */
    private static List<Doc.NestRef> fileLevel(Layout layout) {
        for (Newline n : layout.breaks()) {
            if (!n.under().isEmpty()) {
                return List.of(n.under().get(0));
            }
        }
        return List.of();
    }

    /** How far in the line beginning at {@code start} is written. */
    private static int indentAt(String text, int start) {
        int indent = 0;
        while (start + indent < text.length() && text.charAt(start + indent) == ' ') {
            indent++;
        }
        return indent;
    }

    /**
     * Where the source begins the line the canonical form opens with {@code n}, or null where it
     * opened no line there.
     *
     * <p>Three ways of finding that line, because not every line the canonical form opens is a
     * place's. A comment is written by the carrier that holds it, and a closing bracket is written
     * by the construct; both are asked through what the two texts have in common — the comments in
     * the order they are written, and the code tokens.
     */
    private static Integer lineStartFor(String source, Formatter.CanonicalForm canonical,
            Map<Integer, Place> opened, Pairing pairing, Newline n) {
        Layout layout = canonical.layout();
        int begins = n.offset() + 1 + n.indent();
        Place place = opened.get(begins);
        if (sourceColumn(source, canonical, place, lineAfter(layout.text(), n)) != null) {
            int start = canonical.construction().places().sourcesOf(place).get(0).start();
            return source.lastIndexOf('\n', Math.max(0, start - 1)) + 1;
        }
        if (place != null) {
            return null;   // a place is written there and the source did not open a line for it
        }
        Integer comment = commentLineFor(source, pairing, begins);
        if (comment != null) {
            return comment;
        }
        List<SyntaxToken> had = pairing.hadCode();
        List<SyntaxToken> writes = pairing.writesCode();
        if (had.size() != writes.size()) {
            return null;
        }
        int i = pairing.adjacencyAt(n.offset());
        if (i < 0) {
            return null;
        }
        int at = had.get(i + 1).start();
        int lineStart = source.lastIndexOf('\n', Math.max(0, at - 1)) + 1;
        return source.substring(lineStart, at).isBlank() ? lineStart : null;
    }

    /**
     * Where the source begins the line it wrote the comment the canonical form opens a line with at
     * {@code begins}, or null where the canonical form opens no comment line there or the source
     * did not write that comment on a line of its own.
     *
     * <p>The comments pair up in the order they are written, which is what {@link #comments} rests
     * on too: the formatter writes every comment of a source exactly once.
     *
     * <p>A source that wrote the comment at the end of a line of code has not put it at a column —
     * where it stands is what the rules about comments answer, and this rule would be moving a
     * comment rather than a line.
     *
     * <p>Nor is a comment the canonical form carries somewhere else. That decision is another
     * rule's and this one reads its result: the line the source has for such a comment is one the
     * repair is about to take away, and an indent written onto it would be an expectation about a
     * line that will not be there. The composition finds this rather than the two rules quietly
     * writing over each other, which is how it was found.
     */
    private static Integer commentLineFor(String source, Pairing pairing, int begins) {
        if (pairing.hadComments().size() != pairing.writesComments().size()
                || pairing.hadCode().size() != pairing.writesCode().size()) {
            return null;
        }
        Integer written = pairing.commentWrittenAt(begins);
        if (written == null) {
            return null;
        }
        int at = pairing.hadComments().get(written).start();
        if (pairing.writesInFrontOf(begins) != pairing.hadInFrontOf(at)) {
            return null;   // carried somewhere else, so this is not the line it is written on
        }
        int lineStart = source.lastIndexOf('\n', Math.max(0, at - 1)) + 1;
        return source.substring(lineStart, at).isBlank() ? lineStart : null;
    }

    /**
     * What the spacing rule has against {@code source}.
     *
     * <p>One boundary of the canonical form at a time, and only the ones it writes on a line. Where
     * it breaks a boundary there is no spacing it wrote, so a source that has a space there is not
     * spacing it wrongly — it is breaking somewhere else, and the break rules answer for that. A
     * report that skipped this said of twenty-one boundaries that a space should be another space
     * when what belongs there is a line break.
     *
     * <p>A source that broke a boundary the canonical form writes on a line is this rule's only
     * where no group settles it. Where one does, what the source departed from is that group's
     * decision, and reporting the break here as well would say one thing twice.
     *
     * <p>The two token streams are held side by side, which is sound while they are the same
     * stream. The canonicalization that rewrites a definition's lambda writes tokens the source has
     * not, and there this refuses rather than pairing the wrong two: an alignment it cannot make is
     * not one it should guess.
     */
    static List<Witness> spacing(String source, Formatter.CanonicalForm canonical) {
        return spacing(source, canonical, new Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    static List<Witness> spacing(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        String text = canonical.layout().text();
        List<SyntaxToken> had = pairing.hadCode();
        List<SyntaxToken> writes = pairing.writesCode();
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source has " + had.size() + " tokens and its canonical form "
                            + writes.size() + "; the two cannot be held side by side and this rule"
                            + " asks what the source has between the same two");
        }
        List<Gaps.Boundary> boundaries = between(canonical.construction().doc(), writes.size());
        // At a stop the run holds this rule's answer and then the column's padding, and this is
        // asked about the first of them. Where the source wrote spaces there, all of it is the
        // column's and this says nothing; where it wrote anything else, what it wrote is not
        // padding and the column rule has no answer about it, so this one does — and the round
        // after it, with the separator written, is where the column is asked.
        Map<Integer, String> atAColumn = new LinkedHashMap<>();
        Set<Integer> padded = new LinkedHashSet<>();
        for (CanonicalStop stop : stops(canonical, writes)) {
            atAColumn.put(stop.adjacency(), stop.separator());
            if (padsAfterTheSeparator(source, had.get(stop.adjacency()),
                    had.get(stop.adjacency() + 1), stop.separator())) {
                padded.add(stop.adjacency());
            }
        }
        List<Witness> out = new ArrayList<>();
        for (int i = 0; i + 1 < writes.size(); i++) {
            if (padded.contains(i)) {
                continue;
            }
            String wrote = atAColumn.containsKey(i) ? atAColumn.get(i)
                    : text.substring(writes.get(i).end(), writes.get(i + 1).start());
            if (wrote.indexOf('\n') >= 0) {
                continue;   // the canonical form breaks here, so it writes no spacing
            }
            String has = source.substring(had.get(i).end(), had.get(i + 1).start());
            if (has.equals(wrote) || has.contains("//")) {
                continue;   // what is written around a comment is the comment rules' to say, and
                            // an answer here would be over the characters the comment is made of
            }
            Gaps.Boundary b = boundaries.get(i);
            if (has.indexOf('\n') >= 0 && b.policy() != TokenDoc.Break.NEVER) {
                continue;   // a boundary a group settles, and the source broke it: the group's
                            // decision is what it departed from, and the conditional rule says so
            }
            out.add(new Witness.BetweenTwoTokens(
                    new Witness.Boundary(i, b.joining(), writes.get(i).kind(),
                            writes.get(i + 1).kind()),
                    wrote, has));
        }
        return out;
    }

    /**
     * One stop of the canonical form, and which adjacency of its code tokens it stands at.
     *
     * <p>The layout says where a stop is as an offset into the text it wrote. What a rule holding
     * two texts side by side can use is which pair of tokens it stands between, since that is the
     * one thing the two share — so the offset is read once, here, and everything downstream is
     * about the adjacency.
     */
    record CanonicalStop(ColumnOccurrence occurrence, int adjacency, String separator) {
    }

    /**
     * Whether what the source writes at a stop reads as the separator and then this rule's padding.
     *
     * <p>The canonical form writes a separator and then the spaces that carry the connector out to
     * the column, and this asks whether the source's run comes apart the same way: the separator
     * itself, and after it spaces and nothing else. That is the whole of what divides the two
     * families at a stop, and it is asked in one place because they must neither both answer about
     * the same characters — a conflict the repair refuses — nor both stay silent, which leaves a
     * difference no rule accounts for.
     *
     * <p>Both halves are the question. Asked only whether what stands there is spaces, a run that
     * is <em>empty</em> answers yes — a source that wrote no separator at all would be this rule's,
     * and a one-row table with no space before its arrow would be told that its rows do not line up
     * with each other. And a tab reaches a column as well as spaces do, so a run this admitted on
     * the strength of the column it arrived at would leave a text that is not the canonical form
     * with nothing said against it.
     *
     * <p>Written against {@code separator} rather than against one space, so a stop whose separator
     * is nothing needs no second reading of this: the prefix is there vacuously and all of the run
     * is padding.
     */
    static boolean padsAfterTheSeparator(String source, SyntaxToken before, SyntaxToken after,
            String separator) {
        String run = source.substring(before.end(), after.start());
        return run.startsWith(separator)
                && run.substring(separator.length()).chars().allMatch(c -> c == ' ');
    }

    /**
     * Every stop the canonical form wrote, with the adjacency it stands at.
     *
     * <p>Read by the two rules that have to know about a stop: the column rule, whose units these
     * are, and the spacing rule, which is not asked at one. Two readers of one value, so that a
     * boundary cannot be a stop for the first and an ordinary boundary for the second.
     */
    static List<CanonicalStop> stops(Formatter.CanonicalForm canonical, List<SyntaxToken> writes) {
        List<CanonicalStop> out = new ArrayList<>();
        int i = 0;
        for (ColumnOccurrence stop : canonical.layout().stops()) {
            while (i + 1 < writes.size() && writes.get(i + 1).start() < stop.at()) {
                i++;
            }
            if (i + 1 >= writes.size() || writes.get(i).end() > stop.at()) {
                throw new IllegalStateException(
                        "a column stop at offset " + stop.at() + " stands at no adjacency of the"
                                + " canonical form's tokens; a stop is written between the"
                                + " separator and the connector after it");
            }
            out.add(new CanonicalStop(stop, i,
                    canonical.layout().text().substring(writes.get(i).end(), stop.at())));
        }
        return out;
    }

    /**
     * What the column rule has against {@code source}: for each column of each table, the display
     * column the canonical form writes the connector at, and the ones the source's rows come to.
     *
     * <p>What a row comes to is where its connector stands with the padding the source wrote and
     * everything before it on the line as the canonical form has it — not the column the connector
     * physically occupies in the source. An absolute column is the sum of everything to its left:
     * the indent, every separator, and every column before it on the line. Read that way, a table
     * an author lined up correctly and indented one column too deep departs from this rule at every
     * row, and repairing the indentation is what makes those departures go away — which is a rule
     * reporting somebody else's difference as its own. {@link Witness.Indentation} met the same
     * thing and answers with a step rather than with a column for the same reason.
     *
     * <p>So what is read from the source is the padding, which is this rule's own, and it is said
     * as the column that padding comes to. Where the rest of the line is already canonical the two
     * are the same number, which is every source that has nothing else wrong with it.
     *
     * <p>A row the canonical form writes down the page has no stop, so it is not asked about here.
     * Neither is a row the source broke: its connector opens a line there, and a column is not
     * something a line's first token can be at. What the source did instead is the conditional
     * layout rule's to report, and once that is repaired this is asked again.
     */
    static List<Witness> columns(String source, Formatter.CanonicalForm canonical) {
        return columns(source, canonical, new Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    static List<Witness> columns(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        List<SyntaxToken> had = pairing.hadCode();
        List<SyntaxToken> writes = pairing.writesCode();
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source has " + had.size() + " tokens and its canonical form "
                            + writes.size() + "; the two cannot be held side by side and this rule"
                            + " asks where the source wrote the same connector");
        }
        Map<Columns.Unit, Integer> written = new LinkedHashMap<>();
        for (ColumnDecision decision : canonical.layout().columns()) {
            written.put(decision.unit(), decision.column());
        }
        Map<Columns.Unit, Set<Integer>> hadAt = new LinkedHashMap<>();
        for (CanonicalStop stop : stops(canonical, writes)) {
            int i = stop.adjacency();
            String between = source.substring(had.get(i).end(), had.get(i + 1).start());
            if (between.indexOf('\n') >= 0 || between.contains("//")) {
                continue;
            }
            if (!padsAfterTheSeparator(source, had.get(i), had.get(i + 1), stop.separator())) {
                continue;   // the spacing rule is answering this run; asked again once it has
            }
            // The run comes apart, so what is left of it after the separator is spaces and each of
            // them is one column.
            int padding = between.length() - stop.separator().length();
            hadAt.computeIfAbsent(stop.occurrence().unit(), _ -> new LinkedHashSet<>())
                    .add(stop.occurrence().naturalColumn() + padding);
        }
        List<Witness> out = new ArrayList<>();
        hadAt.forEach((unit, columns) -> {
            Integer column = written.get(unit);
            if (column == null) {
                throw new IllegalStateException(
                        "a row was written to " + unit.stop() + " and the layout says no column is"
                                + " there; a stop and the decision it is written to are made by one"
                                + " run");
            }
            if (!columns.equals(Set.of(column))) {
                out.add(new Witness.AtAColumn(unit, column, List.copyOf(columns)));
            }
        });
        return out;
    }

    /**
     * What the rules about comments have against {@code source}.
     *
     * <p>Two of them. A comment at the end of a line of code has one space in front of it; a comment
     * on a line of its own has the thing it is written above on the next line and no blank between.
     *
     * <p>The comments of the two texts are held side by side, in the order they are written. The
     * formatter writes every comment of a source exactly once — a canonicalization that dropped one
     * is refused before it is laid out — so the two runs pair up, and a source whose count differs
     * is not one this can answer about.
     */
    static List<Witness> comments(String source, Formatter.CanonicalForm canonical) {
        return comments(source, canonical, new Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    static List<Witness> comments(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        String text = canonical.layout().text();
        List<SyntaxToken> had = pairing.hadComments();
        List<SyntaxToken> writes = pairing.writesComments();
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source holds " + had.size() + " comments and its canonical form "
                            + writes.size() + "; the two cannot be held side by side");
        }
        boolean aligned = pairing.hadCode().size() == pairing.writesCode().size();
        int lastWritten = lastStandingIn(text);
        List<Witness> out = new ArrayList<>();
        for (int i = 0; i < had.size(); i++) {
            Witness.Comment unit = new Witness.Comment(had.get(i).start());
            if (aligned) {
                int wroteAt = pairing.writesInFrontOf(writes.get(i).start());
                int hasAt = pairing.hadInFrontOf(had.get(i).start());
                if (wroteAt != hasAt) {
                    out.add(new Witness.CommentCarrier(unit, wroteAt, hasAt));
                    continue;   // what stands beside it is asked where it is written, not where
                                // the source happened to leave it
                }
            }
            String hadBefore = before(source, had.get(i));
            String writesBefore = before(text, writes.get(i));
            if (!opensItsLine(text, writes.get(i)) && !opensItsLine(source, had.get(i))
                    && !hadBefore.equals(writesBefore)) {
                out.add(new Witness.TrailingComment(unit, writesBefore, hadBefore));
            }
            if (opensItsLine(text, writes.get(i))
                    && writes.get(i).end() <= lastWritten) {
                int wrote = newlines(after(text, writes.get(i)));
                int has = newlines(after(source, had.get(i)));
                if (wrote != has) {
                    out.add(new Witness.CommentAbove(unit, wrote, has));
                }
            }
        }
        return out;
    }

    /**
     * The last offset of {@code text} something is written at, or -1 where nothing is.
     *
     * <p>What it answers is whether anything is written after a comment. Such a comment is written
     * above nothing, so what stands under it is not the distance the rule about a comment's line
     * answers about — it is the end of the file, and how a file ends is the file's own rule.
     * Answered there as well, the two would both write the same newline.
     *
     * <p>Read once for a whole run of comments. Asked comment by comment, of the stretch after each
     * of them, it is the length of that stretch every time and the last comment of a file is as far
     * from its end as the first.
     */
    private static int lastStandingIn(String text) {
        for (int i = text.length() - 1; i >= 0; i--) {
            if (!Character.isWhitespace(text.charAt(i))) {
                return i;
            }
        }
        return -1;
    }

    /**
     * Whether nothing but whitespace stands in front of a comment on its line.
     *
     * <p>Read from the line rather than from the stretch back to the code before it. At the top of
     * a file there is no code in front of a comment, so that stretch is empty and every source's
     * first comment came back as one at the end of a line — which is a rule that answers about the
     * space in front of it and not about the lines around it.
     */
    private static boolean opensItsLine(String text, SyntaxToken comment) {
        int lineStart = text.lastIndexOf('\n', Math.max(0, comment.start() - 1)) + 1;
        return text.substring(lineStart, comment.start()).isBlank();
    }

    /** What stands between a comment and the code before it, back to the line it starts on. */
    private static String before(String text, SyntaxToken comment) {
        int from = comment.start();
        while (from > 0 && Character.isWhitespace(text.charAt(from - 1))) {
            from--;
        }
        return text.substring(from, comment.start());
    }

    /** What stands between a comment and whatever is written after it. */
    private static String after(String text, SyntaxToken comment) {
        int to = comment.end();
        while (to < text.length() && Character.isWhitespace(text.charAt(to))) {
            to++;
        }
        return text.substring(comment.end(), to);
    }

    /** The file's comments, in the order they are written. */
    static List<SyntaxToken> comments(SyntaxNode node) {
        List<SyntaxToken> out = new ArrayList<>();
        gather(node, out);
        return out;
    }

    private static void gather(SyntaxNode node, List<SyntaxToken> out) {
        for (SyntaxElement e : node.children()) {
            switch (e) {
                case SyntaxNode n -> gather(n, out);
                case SyntaxToken t -> {
                    if (t.kind() == SyntaxKind.LINE_COMMENT) {
                        out.add(t);
                    }
                }
            }
        }
    }

    /**
     * What the separation rule has against {@code source}.
     *
     * <p>One witness per pair of adjacent top-level items, and the answer is a count of blank
     * lines. The canonical form's is read from the decision — whether it wrote the break it writes
     * for that obligation — and the source's from the text, which is all a source has.
     *
     * <p>The gap is taken whole, comments and all. A comment written between two items is carried
     * by the second, so what stands between the first and that comment is the separation, and blank
     * lines anywhere in the gap are lines the canonical form does not write.
     */
    static List<Witness> separation(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        return separation(source, canonical);   // it reads the places, not the tokens
    }

    /** What the separation rule has against {@code source}. */
    static List<Witness> separation(String source, Formatter.CanonicalForm canonical) {
        List<Place> items = topLevel(canonical);
        int[] separating = separatingBreaks(canonical);
        List<Witness> out = new ArrayList<>();
        for (int i = 0; i + 1 < items.size(); i++) {
            Place previous = items.get(i);
            Place next = items.get(i + 1);
            int writes = separates(canonical, separating, previous, next) ? 1 : 0;
            Integer has = blankLines(source, canonical, previous, next);
            if (has != null && has != writes) {
                out.add(new Witness.Separation(new Witness.Items(previous, next), writes, has));
            }
        }
        return out;
    }

    /**
     * What the conditional-layout rule has against {@code source}.
     *
     * <p>One witness per group the width decided. A group is not its boundaries: written down the
     * page it moves every one of them, and what was decided was whether the line it would take fits.
     *
     * <p>Matched against the opportunities rather than against the breaks. Where the canonical form
     * keeps a group whole there is no break of its to point at, and a source that broke inside it
     * has still departed from the decision — so what is asked of each opportunity is whether the
     * source has a line ending at the same place.
     *
     * <p>Every one of them, and not whether any broke. A group written down the page breaks at each
     * opportunity it settles, so a source that broke some of them and ran the rest together has not
     * laid it out that way: the decision is one and it is about all of them.
     *
     * <p>What the witness carries is the opportunity, though, and not the group's two answers. A
     * source that broke some of them departed at the ones it ran together, and a witness holding
     * only whether the canonical form keeps the group whole against whether the source broke it
     * anywhere has thrown away which those were — leaving a report that has to name a difference
     * with two values that are equal in exactly the case it was asked about. The first of them is
     * what the witness stands at; the repair writes them all.
     *
     * <p>Two departures, and they are not one rule. A source can disagree about the form — it wrote
     * whole what the canonical form writes down the page, or the other way about — and it can agree
     * about the form and run some of the places together. The first is a choice between two ways of
     * writing the construct and is named by whatever made that choice; the second is about a place
     * and holds whatever made it, so the two are told apart here rather than in the report.
     *
     * <p>A group written down the page because it holds a forced break is still this family's. What
     * the forced decision settled is why the group is not flat, not whether it is, and a source can
     * depart from it either way — so the witness carries that reason and lets the rule be named
     * from it, rather than being answered for by a rule about the width that decided nothing here.
     */
    static List<Witness> conditional(String source, Formatter.CanonicalForm canonical) {
        return conditional(source, canonical, new Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    static List<Witness> conditional(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        Layout layout = canonical.layout();
        List<SyntaxToken> had = pairing.hadCode();
        List<SyntaxToken> writes = pairing.writesCode();
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source has " + had.size() + " tokens and its canonical form "
                            + writes.size() + "; the two cannot be held side by side");
        }
        Map<Doc.GroupRef, Outcome> outcomes = new IdentityHashMap<>();
        for (GroupDecision d : layout.decisions()) {
            outcomes.put(d.group(), d.outcome());
        }
        Map<Doc.GroupRef, Opportunity> parted = new IdentityHashMap<>();
        Map<Doc.GroupRef, Boolean> brokeAnywhere = new IdentityHashMap<>();
        for (Opportunity o : layout.opportunities()) {
            boolean brokeThere = brokeInSource(source, pairing, o.at());
            brokeAnywhere.merge(o.settledBy(), brokeThere, (a, b) -> a || b);
            if (brokeThere == o.broke()) {
                continue;   // the source settled this place the way the group did
            }
            Opportunity already = parted.get(o.settledBy());
            if (already == null || o.at() < already.at()) {
                parted.put(o.settledBy(), o);
            }
        }

        List<Opportunity> firsts = new ArrayList<>(parted.values());
        // By where they stand, so that the report a source gets does not depend on the order the
        // groups happened to be met in.
        firsts.sort(Comparator.comparingInt(Opportunity::at));
        List<Witness> out = new ArrayList<>();
        for (Opportunity o : firsts) {
            Witness.Group unit = new Witness.Group(o.settledBy(), o.at());
            Outcome why = outcomes.get(o.settledBy());
            boolean canonicalIsWhole = why instanceof Outcome.Flat;
            boolean sourceIsWhole = !Boolean.TRUE.equals(brokeAnywhere.get(o.settledBy()));
            if (canonicalIsWhole != sourceIsWhole) {
                out.add(new Witness.Conditional(unit, canonicalIsWhole, sourceIsWhole, why));
            } else {
                out.add(new Witness.RunTogether(unit, o.broke(), !o.broke()));
            }
        }
        return out;
    }

    /**
     * What the rule about the end of a line has against {@code source}: the lines it wrote
     * something at the end of.
     *
     * <p>Asked of the source's lines directly. The expectation is nothing, and that is what the
     * canonical form writes at the end of every line it has, so there is no unit of the canonical
     * form to find the source's answer at — which also makes this the one rule that can answer
     * about a source whose tokens the canonical form rewrites.
     *
     * <p>The last line of a source is one of these only where nothing but whitespace is written on
     * it. Anywhere else what stands after the last newline is what the file's own rule is about —
     * how a file ends — and its repair writes the whole of that stretch, so answering here as well
     * would be two rules over the same characters.
     */
    static List<Witness> lineEnds(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        return lineEnds(source, canonical);   // it reads the source's lines, not the tokens
    }

    /** What the rule about the end of a line has against {@code source}. */
    static List<Witness> lineEnds(String source, Formatter.CanonicalForm canonical) {
        List<Witness> out = new ArrayList<>();
        int from = 0;
        while (true) {
            int newline = source.indexOf('\n', from);
            int ends = newline < 0 ? source.length() : newline;
            int at = ends;
            while (at > from && (source.charAt(at - 1) == ' ' || source.charAt(at - 1) == '\t')) {
                at--;
            }
            if (at < ends && (newline >= 0 || (from > 0 && at == from))) {
                out.add(new Witness.AtTheEndOfALine(new Witness.LineEnd(at), "",
                        source.substring(at, ends)));
            }
            if (newline < 0) {
                return out;
            }
            from = newline + 1;
        }
    }

    /**
     * What the rule about a group's breaks has against {@code source}: the places it settled by
     * breaking, where the source ended a different number of lines.
     *
     * <p>One line ends at each of them. A blank line inside a construct is written where the author
     * wrote a paragraph break between two members, and that is a forced break with an obligation of
     * its own — so a source that left a blank line at a place a group settles has departed from
     * something, and until this rule was a value it was the one departure nothing could name: the
     * group did break there, so the conditional rule agrees, and no obligation stands there for the
     * forced rules to count lines at.
     *
     * <p>Only where the source ended a line there. One that ran the boundary together departed from
     * the group's decision, which {@link #conditional} answers for, and saying it here as well
     * would say one thing twice.
     *
     * <p>And not where an obligation breaks the same boundary. Two rules would count the same
     * newlines from their own units and one of them would be wrong about how many belong there.
     */
    static List<Witness> settled(String source, Formatter.CanonicalForm canonical) {
        return settled(source, canonical, new Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    static List<Witness> settled(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        Layout layout = canonical.layout();
        String text = layout.text();
        List<SyntaxToken> had = pairing.hadCode();
        List<SyntaxToken> writes = pairing.writesCode();
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source has " + had.size() + " tokens and its canonical form "
                            + writes.size() + "; the two cannot be held side by side");
        }
        Set<Integer> obliged = new LinkedHashSet<>();
        for (Newline n : layout.breaks()) {
            if (n.cause() instanceof Newline.Cause.Forced) {
                obliged.add(pairing.adjacencyAt(n.offset()));
            }
        }
        List<Witness> out = new ArrayList<>();
        Set<Integer> seen = new LinkedHashSet<>();
        for (Opportunity o : layout.opportunities()) {
            if (!o.broke()) {
                continue;
            }
            int i = pairing.adjacencyAt(o.at());
            if (i < 0 || obliged.contains(i) || !seen.add(i)) {
                continue;
            }
            String has = source.substring(had.get(i).end(), had.get(i + 1).start());
            String wrote = text.substring(writes.get(i).end(), writes.get(i + 1).start());
            if (has.contains("//") || wrote.contains("//")) {
                continue;   // what is written around a comment is the comment rules'
            }
            if (newlines(has) > 0 && newlines(has) != newlines(wrote)) {
                out.add(new Witness.Settled(new Witness.BrokenBoundary(i), newlines(wrote),
                        newlines(has)));
            }
        }
        return out;
    }

    /**
     * What the forced-layout rules have against {@code source}: the boundaries the canonical form
     * breaks whatever the width and the source wrote on a line.
     *
     * <p>One witness per boundary, which for these rules is one per unit. The separation rule is
     * not among them — its unit is a pair of items and its answer a count of blank lines, and
     * {@link #separation} says it.
     *
     * <p>How many lines end there and not whether one does. A construct writes its members one to a
     * line, so a source that left a blank line between two of them has as much departed from that
     * as one that ran them together — and where several obligations break at one adjacency, what
     * they say together is the count.
     *
     * <p>A break the source wrote at an adjacency no forced rule breaks is not reported here. The
     * rule says a line ends where it does, not that no other line may, and what answers for such a
     * break is the group whose opportunity it sits at.
     *
     * <p>A pair of top-level items is left to the separation rule, which counts the same lines from
     * its own unit, and a gap holding a comment to the rules about comments.
     */
    static List<Witness> forced(String source, Formatter.CanonicalForm canonical) {
        return forced(source, canonical, new Pairing(source, canonical));
    }

    /** The same, for a caller that has already read the two texts' tokens. */
    static List<Witness> forced(String source, Formatter.CanonicalForm canonical,
            Pairing pairing) {
        Layout layout = canonical.layout();
        String text = layout.text();
        List<SyntaxToken> had = pairing.hadCode();
        List<SyntaxToken> writes = pairing.writesCode();
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source has " + had.size() + " tokens and its canonical form "
                            + writes.size() + "; the two cannot be held side by side");
        }
        // The obligations that break at each adjacency, in the order they are written. Several
        // stand at one where a blank line or a comment is written between two tokens, and what the
        // rules say together is how many lines end there.
        Map<Integer, List<Obligation>> at = new LinkedHashMap<>();
        List<Witness> out = new ArrayList<>();
        for (Newline n : layout.breaks()) {
            if (!(n.cause() instanceof Newline.Cause.Forced f)) {
                continue;
            }
            if (writes.isEmpty() || n.offset() >= writes.get(writes.size() - 1).end()) {
                // Past the last token there are two boundaries where a comment ends the file: the
                // one in front of it, and the file's own after it. They are two rules and they are
                // held against two stretches, or the same newline would be answered for twice.
                if (f.obligation() == Obligation.A_FILE_ENDS_WITH_ONE_NEWLINE) {
                    int ends = trailingNewlines(source);
                    if (ends != 1) {
                        out.add(new Witness.Forced(new Witness.ForcedBoundary(-1, f.obligation()),
                                1, ends));
                    }
                } else {
                    int wrote = newlines(aboveTheLastComment(text, pairing.writesCode(),
                            pairing.writesComments()));
                    int has = newlines(aboveTheLastComment(source, pairing.hadCode(),
                            pairing.hadComments()));
                    if (wrote != has) {
                        out.add(new Witness.Forced(new Witness.ForcedBoundary(-2, f.obligation()),
                                wrote, has));
                    }
                }
                continue;
            }
            int i = pairing.adjacencyAt(n.offset());
            if (i >= 0) {
                at.computeIfAbsent(i, _ -> new ArrayList<>()).add(f.obligation());
            }
        }
        for (Map.Entry<Integer, List<Obligation>> e : at.entrySet()) {
            int i = e.getKey();
            if (e.getValue().contains(Obligation.A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS)) {
                continue;   // a pair of top-level items, and the separation rule counts its lines
            }
            String has = source.substring(had.get(i).end(), had.get(i + 1).start());
            String wrote = text.substring(writes.get(i).end(), writes.get(i + 1).start());
            if (has.contains("//") || wrote.contains("//")) {
                continue;   // what is written around a comment is the comment rules'
            }
            if (newlines(has) != newlines(wrote)) {
                out.add(new Witness.Forced(new Witness.ForcedBoundary(i, e.getValue().get(0)),
                        newlines(wrote), newlines(has)));
            }
        }
        return out;
    }

    /**
     * What stands between a text's last code token and the comment written after it, or nothing
     * where no comment is.
     *
     * <p>Asked with the tokens the caller has already read. Read from the text alone it is another
     * parse of the whole file, made to answer about its last few characters.
     */
    static String aboveTheLastComment(String text, List<SyntaxToken> code,
            List<SyntaxToken> comments) {
        if (code.isEmpty() || comments.isEmpty()) {
            return "";
        }
        int from = code.get(code.size() - 1).end();
        SyntaxToken last = comments.get(comments.size() - 1);
        return last.start() < from ? "" : text.substring(from, last.start());
    }

    /** How many lines a text ends with, counted from its last code. */
    private static int trailingNewlines(String text) {
        int n = 0;
        for (int i = text.length() - 1; i >= 0 && Character.isWhitespace(text.charAt(i)); i--) {
            if (text.charAt(i) == '\n') {
                n++;
            }
        }
        return n;
    }

    private static int newlines(String text) {
        int n = 0;
        for (int i = 0; i < text.length(); i++) {
            if (text.charAt(i) == '\n') {
                n++;
            }
        }
        return n;
    }

    /**
     * Whether the source broke at the adjacency the canonical form has an opportunity at.
     *
     * <p>The opportunity stands between two of the canonical form's tokens, and the source's
     * answer is what it wrote between the same two of its own.
     */
    static boolean brokeInSource(String source, Pairing pairing, int at) {
        int i = pairing.adjacencyAt(at);
        if (i < 0) {
            return false;
        }
        List<SyntaxToken> had = pairing.hadCode();
        return brokeBetween(source, had.get(i).end(), had.get(i + 1).start());
    }

    /** Whether a line ends somewhere in {@code [from, to)} of {@code text}. */
    private static boolean brokeBetween(String text, int from, int to) {
        for (int i = from; i < to; i++) {
            if (text.charAt(i) == '\n') {
                return true;
            }
        }
        return false;
    }

    /** The file's items, in the order the canonical form writes them. */
    private static List<Place> topLevel(Formatter.CanonicalForm canonical) {
        Place file = canonical.construction().places().file();
        List<Place> out = new ArrayList<>();
        for (Place p : canonical.construction().places().made()) {
            if (p.parent() == file && canonical.layout().extents().containsKey(p)) {
                out.add(p);
            }
        }
        out.sort(java.util.Comparator.comparingInt(
                p -> canonical.layout().extents().get(p).start()));
        return out;
    }

    /**
     * Where the canonical form wrote the break it writes to separate two items, in order.
     *
     * <p>Read once for a whole run of pairs. A file's items and its breaks both grow with it, so
     * asked pair by pair of every break the rule costs the two multiplied together.
     */
    private static int[] separatingBreaks(Formatter.CanonicalForm canonical) {
        List<Integer> out = new ArrayList<>();
        for (Newline n : canonical.layout().breaks()) {
            if (n.cause() instanceof Newline.Cause.Forced f
                    && f.obligation() == Obligation.A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS) {
                out.add(n.offset());
            }
        }
        int[] offsets = new int[out.size()];
        for (int i = 0; i < offsets.length; i++) {
            offsets[i] = out.get(i);
        }
        Arrays.sort(offsets);
        return offsets;
    }

    /** Whether the canonical form wrote the break it writes to separate two items. */
    private static boolean separates(Formatter.CanonicalForm canonical, int[] separating,
            Place previous, Place next) {
        int from = canonical.layout().extents().get(previous).end();
        int to = canonical.layout().extents().get(next).start();
        int at = Arrays.binarySearch(separating, from);
        int first = at >= 0 ? at : -(at + 1);   // the first break at or after the first item's end
        return first < separating.length && separating[first] < to;
    }

    /** How many lines the source left blank between two items, or null where it has nothing for
     *  one of them. */
    private static Integer blankLines(String source, Formatter.CanonicalForm canonical,
            Place previous, Place next) {
        List<Written> before = canonical.construction().places().sourcesOf(previous);
        List<Written> after = canonical.construction().places().sourcesOf(next);
        if (before.isEmpty() || after.isEmpty()) {
            return null;
        }
        int from = before.get(before.size() - 1).end();
        int to = after.get(0).start();
        if (from > to || to > source.length()) {
            return null;
        }
        String[] lines = source.substring(from, to).split("\n", -1);
        int blank = 0;
        for (int i = 1; i + 1 < lines.length; i++) {
            if (!lines[i].isBlank()) {
                break;   // what opens the second item's block: its own line, or a comment it carries
            }
            blank++;
        }
        return blank;
    }

    /**
     * The boundaries of {@code doc} that stand between two of its code tokens, in the order they
     * are written and one per adjacency.
     *
     * <p>{@link Gaps#boundaries} reports the ones at the ends too — in front of a leading comment,
     * and after the last token where the file's own break is — and those join nothing. Left in, the
     * list is off by one from the adjacencies and every construct a witness names past that point
     * is the wrong one. The count is held rather than assumed.
     */
    private static List<Gaps.Boundary> between(TokenDoc doc, int tokens) {
        List<Gaps.Boundary> out = new ArrayList<>();
        for (Gaps.Boundary b : Gaps.boundaries(doc)) {
            if (b.left() != null && b.right() != null) {
                out.add(b);
            }
        }
        if (out.size() != tokens - 1) {
            throw new IllegalStateException(
                    "the canonical form has " + tokens + " tokens and " + out.size()
                            + " boundaries between two of them; there is one per adjacency, and a"
                            + " witness names the construct joining a boundary by that count");
        }
        return out;
    }

    /** The file's tokens, comments and whitespace left out. */
    static List<SyntaxToken> code(SyntaxNode node) {
        List<SyntaxToken> out = new ArrayList<>();
        collect(node, out);
        return out;
    }

    private static void collect(SyntaxNode node, List<SyntaxToken> out) {
        for (SyntaxElement e : node.children()) {
            switch (e) {
                case SyntaxNode n -> collect(n, out);
                case SyntaxToken t -> {
                    if (!t.isTrivia() && t.kind() != SyntaxKind.LINE_COMMENT
                            && t.kind() != SyntaxKind.EOF) {
                        out.add(t);
                    }
                }
            }
        }
    }

    /** How much further in the canonical form writes {@code inner} than {@code outer}, or null
     *  where either level has no line of its own for the rule to have written a column for. */
    private static Integer step(Map<Doc.NestRef, Integer> written, Doc.NestRef outer,
            Doc.NestRef inner) {
        Integer in = written.get(inner);
        Integer out = outer == null ? Integer.valueOf(0) : written.get(outer);
        return in == null || out == null ? null : in - out;
    }

    /**
     * The steps the source wrote at a pair of levels, in order and without repeats, or null where
     * it wrote no line for either of them.
     *
     * <p>More than one where the source was not consistent about the inner level. That is one
     * decision it got wrong and several columns it wrote, not several decisions — the rule was
     * evaluated once and says one step.
     *
     * <p>The outer level has to be one column. Where it is not, its own pair is the unit that is
     * wrong, and asking this one about a step measured from a column that moves would name a
     * number neither level has.
     */
    private static List<Integer> sourceSteps(Map<Doc.NestRef, Set<Integer>> had, Doc.NestRef outer,
            Doc.NestRef inner) {
        Set<Integer> in = had.get(inner);
        Set<Integer> out = outer == null ? Set.of(0) : had.get(outer);
        if (in == null || out == null || out.size() != 1) {
            return null;
        }
        int from = out.iterator().next();
        return in.stream().map(c -> c - from).distinct().sorted().toList();
    }

    /** Which place each offset of the canonical text opens, taking the widest where several begin
     *  together: the line belongs to what holds the rest of it. An offset, not a column — an extent
     *  indexes the text, and only a layout's own width arithmetic is in columns. */
    private static Map<Integer, Place> placesByStart(Layout layout) {
        Map<Integer, Place> out = new LinkedHashMap<>();
        layout.extents().forEach((place, extent) -> {
            Place standing = out.get(extent.start());
            if (standing == null || layout.extents().get(standing).end() < extent.end()) {
                out.put(extent.start(), place);
            }
        });
        return out;
    }

    /** What the canonical form writes on the line {@code n} opens. */
    private static String lineAfter(String text, Newline n) {
        int from = n.offset() + 1;
        int to = text.indexOf('\n', from);
        return text.substring(from, to < 0 ? text.length() : to).stripLeading();
    }

    /**
     * How far in the source wrote the line it holds {@code place} on, or null where it did not
     * begin a line with it.
     *
     * <p>The element is not always the first thing on that line. A match arm's {@code |} is written
     * by the canonical form's place and is the match expression's own token in the source, so a
     * source that broke before the arm has the bar in front of the node the place was written from.
     * What is asked is therefore whether the source's line begins the way the canonical one does up
     * to the element — which a line the source ran on into does not: a {@code let} the source left
     * after an opening brace has that brace in front of it, and the canonical line for it has not.
     */
    private static Integer sourceColumn(String source, Formatter.CanonicalForm canonical,
            Place place, String canonicalLine) {
        if (place == null) {
            return null;
        }
        List<Written> from = canonical.construction().places().sourcesOf(place);
        if (from.size() != 1) {
            return null;   // written from nothing, or from several elements that are not one column
        }
        int start = from.get(0).start();
        if (start > source.length()) {
            return null;
        }
        int lineStart = source.lastIndexOf('\n', Math.max(0, start - 1)) + 1;
        String before = source.substring(lineStart, start).strip();
        if (!before.isEmpty() && !canonicalLine.startsWith(before)) {
            return null;   // the source ran on into this line rather than opening one for it
        }
        int indent = 0;
        while (lineStart + indent < source.length() && source.charAt(lineStart + indent) == ' ') {
            indent++;
        }
        return indent;
    }
}
