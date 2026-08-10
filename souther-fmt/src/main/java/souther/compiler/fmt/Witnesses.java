package souther.compiler.fmt;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
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
 * <p>One family at a time. The indentation rule is here; the others are added as each one's unit and
 * expectation become values.
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
        Layout layout = canonical.layout();
        Map<Doc.NestRef, Integer> written = new IdentityHashMap<>();
        Map<Doc.NestRef, Set<Integer>> had = new IdentityHashMap<>();
        Map<Integer, Place> opened = placesByStart(layout);

        for (Newline n : layout.breaks()) {
            if (n.under().isEmpty() || !n.indents()) {
                continue;   // a line the file holds under no nesting, or one with nothing on it:
                            // neither is a line written at a level's column
            }
            Doc.NestRef innermost = n.under().get(n.under().size() - 1);
            Integer already = written.put(innermost, n.indent());
            if (already != null && already != n.indent()) {
                throw new IllegalStateException(
                        "one level of nesting, written at column " + already + " and at column "
                                + n.indent() + "; a level has one column and the layout wrote two");
            }
            Integer column = columnFor(source, canonical, opened, n);
            if (column != null) {
                had.computeIfAbsent(innermost, _ -> new LinkedHashSet<>()).add(column);
            }
        }

        List<Witness> out = new ArrayList<>();
        Set<Witness.Levels> seen = new LinkedHashSet<>();
        for (Newline n : layout.breaks()) {
            for (int i = 0; i < n.under().size(); i++) {
                Doc.NestRef inner = n.under().get(i);
                Doc.NestRef outer = i == 0 ? null : n.under().get(i - 1);
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
     * Where the source begins the line each break of the canonical form opens, for the breaks whose
     * line the source opened too.
     *
     * <p>The offset that line starts at, so that what stands in front of the first thing on it is
     * the indent a repair writes over. A break the source has no line for is not here: the source
     * broke somewhere else, and moving an indent would be answering a question about a line nobody
     * wrote.
     */
    static Map<Newline, Integer> sourceLines(String source, Formatter.CanonicalForm canonical) {
        Layout layout = canonical.layout();
        Map<Integer, Place> opened = placesByStart(layout);
        Map<Newline, Integer> out = new LinkedHashMap<>();
        for (Newline n : layout.breaks()) {
            if (!n.indents()) {
                continue;   // its line has nothing on it, so there is no indent to repair
            }
            Integer start = lineStartFor(source, canonical, opened, n);
            if (start != null) {
                out.put(n, start);
            }
        }
        return out;
    }

    /**
     * How far in the source wrote the line the canonical form opens with {@code n}, or null where
     * it opened no line there.
     *
     * <p>Two ways of finding that line, because not every line the canonical form opens is a
     * place's. A closing bracket takes a line of its own and is written by the construct rather
     * than at a place, so a break in front of one is found through the token the two texts have in
     * common instead.
     */
    private static Integer columnFor(String source, Formatter.CanonicalForm canonical,
            Map<Integer, Place> opened, Newline n) {
        Integer start = lineStartFor(source, canonical, opened, n);
        if (start == null) {
            return null;
        }
        int indent = 0;
        while (start + indent < source.length() && source.charAt(start + indent) == ' ') {
            indent++;
        }
        return indent;
    }

    /** Where the source begins the line, by the same two ways. */
    private static Integer lineStartFor(String source, Formatter.CanonicalForm canonical,
            Map<Integer, Place> opened, Newline n) {
        Layout layout = canonical.layout();
        Place place = opened.get(n.offset() + 1 + n.indent());
        if (sourceColumn(source, canonical, place, lineAfter(layout.text(), n)) != null) {
            int start = canonical.construction().places().sourcesOf(place).get(0).start();
            return source.lastIndexOf('\n', Math.max(0, start - 1)) + 1;
        }
        if (place != null) {
            return null;   // a place is written there and the source did not open a line for it
        }
        List<SyntaxToken> had = code(CstParser.parse(source).root());
        List<SyntaxToken> writes = code(CstParser.parse(layout.text()).root());
        if (had.size() != writes.size()) {
            return null;
        }
        for (int i = 0; i + 1 < writes.size(); i++) {
            if (writes.get(i).end() > n.offset() || n.offset() > writes.get(i + 1).start()) {
                continue;
            }
            int at = had.get(i + 1).start();
            int lineStart = source.lastIndexOf('\n', Math.max(0, at - 1)) + 1;
            return source.substring(lineStart, at).isBlank() ? lineStart : null;
        }
        return null;
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
        String text = canonical.layout().text();
        List<SyntaxToken> had = code(CstParser.parse(source).root());
        List<SyntaxToken> writes = code(CstParser.parse(text).root());
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source has " + had.size() + " tokens and its canonical form "
                            + writes.size() + "; the two cannot be held side by side and this rule"
                            + " asks what the source has between the same two");
        }
        List<Gaps.Boundary> boundaries = between(canonical.construction().doc(), writes.size());
        List<Witness> out = new ArrayList<>();
        for (int i = 0; i + 1 < writes.size(); i++) {
            String wrote = text.substring(writes.get(i).end(), writes.get(i + 1).start());
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
        String text = canonical.layout().text();
        List<SyntaxToken> had = comments(CstParser.parse(source).root());
        List<SyntaxToken> writes = comments(CstParser.parse(text).root());
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source holds " + had.size() + " comments and its canonical form "
                            + writes.size() + "; the two cannot be held side by side");
        }
        List<SyntaxToken> hadCode = code(CstParser.parse(source).root());
        List<SyntaxToken> writesCode = code(CstParser.parse(text).root());
        boolean aligned = hadCode.size() == writesCode.size();
        List<Witness> out = new ArrayList<>();
        for (int i = 0; i < had.size(); i++) {
            Witness.Comment unit = new Witness.Comment(had.get(i).start());
            if (aligned) {
                int wroteAt = follows(writesCode, writes.get(i).start());
                int hasAt = follows(hadCode, had.get(i).start());
                if (wroteAt != hasAt) {
                    out.add(new Witness.CommentCarrier(unit, wroteAt, hasAt));
                    continue;   // what stands beside it is asked where it is written, not where
                                // the source happened to leave it
                }
            }
            String hadBefore = before(source, had.get(i));
            String writesBefore = before(text, writes.get(i));
            if (writesBefore.indexOf('\n') < 0 && hadBefore.indexOf('\n') < 0
                    && !hadBefore.equals(writesBefore)) {
                out.add(new Witness.TrailingComment(unit, writesBefore, hadBefore));
            }
            if (writesBefore.indexOf('\n') >= 0) {
                int wrote = newlines(after(text, writes.get(i)));
                int has = newlines(after(source, had.get(i)));
                if (wrote != has) {
                    out.add(new Witness.CommentAbove(unit, wrote, has));
                }
            }
        }
        return out;
    }

    /** Which code token a comment stands after, as its index, or -1 where none is in front of it. */
    private static int follows(List<SyntaxToken> tokens, int at) {
        int found = -1;
        for (int i = 0; i < tokens.size(); i++) {
            if (tokens.get(i).end() <= at) {
                found = i;
            }
        }
        return found;
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
    static List<Witness> separation(String source, Formatter.CanonicalForm canonical) {
        List<Place> items = topLevel(canonical);
        List<Witness> out = new ArrayList<>();
        for (int i = 0; i + 1 < items.size(); i++) {
            Place previous = items.get(i);
            Place next = items.get(i + 1);
            int writes = separates(canonical, previous, next) ? 1 : 0;
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
     * <p>A group written down the page because it holds a forced break is still this rule's. What
     * the forced decision settled is why the group is not flat, not whether it is: the group broke,
     * every opportunity it settles broke with it, and a source that ran them together departed from
     * that. What such a witness never says is that the canonical form keeps the group whole, which
     * is the answer that would tell an author to close up a line a comment holds open.
     */
    static List<Witness> conditional(String source, Formatter.CanonicalForm canonical) {
        Layout layout = canonical.layout();
        List<SyntaxToken> had = code(CstParser.parse(source).root());
        List<SyntaxToken> writes = code(CstParser.parse(layout.text()).root());
        if (had.size() != writes.size()) {
            throw new NoCorrespondence(
                    "the source has " + had.size() + " tokens and its canonical form "
                            + writes.size() + "; the two cannot be held side by side");
        }
        Map<Doc.GroupRef, Outcome> outcomes = new IdentityHashMap<>();
        Map<Doc.GroupRef, Integer> where = new IdentityHashMap<>();
        for (GroupDecision d : layout.decisions()) {
            outcomes.put(d.group(), d.outcome());
        }
        Map<Doc.GroupRef, Boolean> broken = new IdentityHashMap<>();
        Map<Doc.GroupRef, Boolean> agrees = new IdentityHashMap<>();
        for (Opportunity o : layout.opportunities()) {
            where.merge(o.settledBy(), o.at(), Math::min);
            boolean brokeThere = brokeInSource(source, had, writes, o.at());
            Boolean already = broken.get(o.settledBy());
            broken.put(o.settledBy(), (already != null && already) || brokeThere);
            // A group written down the page breaks at every opportunity it settles, so a source
            // that broke some of them and not the rest has not laid it out that way either. The
            // decision is one and it is about all of them.
            Boolean sofar = agrees.get(o.settledBy());
            agrees.put(o.settledBy(),
                    (sofar == null || sofar) && brokeThere == o.broke());
        }

        List<Witness> out = new ArrayList<>();
        for (Map.Entry<Doc.GroupRef, Integer> e : where.entrySet()) {
            Outcome outcome = outcomes.get(e.getKey());
            boolean whole = outcome instanceof Outcome.Flat;
            boolean sourceWhole = !Boolean.TRUE.equals(broken.get(e.getKey()));
            if (!Boolean.TRUE.equals(agrees.get(e.getKey()))) {
                out.add(new Witness.Conditional(new Witness.Group(e.getKey(), e.getValue()),
                        whole, sourceWhole));
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
        Layout layout = canonical.layout();
        List<SyntaxToken> had = code(CstParser.parse(source).root());
        List<SyntaxToken> writes = code(CstParser.parse(layout.text()).root());
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
                // past the last token: the break that ends the file, and what the source has for it
                // is whether it ends with a newline and with one
                int ends = trailingNewlines(source);
                if (ends != 1) {
                    out.add(new Witness.Forced(new Witness.ForcedBoundary(-1, f.obligation()),
                            1, ends));
                }
                continue;
            }
            int i = adjacencyAt(writes, n.offset());
            if (i >= 0) {
                at.computeIfAbsent(i, _ -> new ArrayList<>()).add(f.obligation());
            }
        }
        String text = layout.text();
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

    /** Which adjacency of {@code tokens} the offset {@code at} stands in, or -1 where it stands
     *  before the first of them. */
    private static int adjacencyAt(List<SyntaxToken> tokens, int at) {
        for (int i = 0; i + 1 < tokens.size(); i++) {
            if (tokens.get(i).end() <= at && at <= tokens.get(i + 1).start()) {
                return i;
            }
        }
        return -1;
    }

    /**
     * Whether the source broke at the adjacency the canonical form has an opportunity at.
     *
     * <p>The opportunity stands between two of the canonical form's tokens, and the source's
     * answer is what it wrote between the same two of its own.
     */
    private static boolean brokeInSource(String source, List<SyntaxToken> had,
            List<SyntaxToken> writes, int at) {
        for (int i = 0; i + 1 < writes.size(); i++) {
            if (writes.get(i).end() <= at && at <= writes.get(i + 1).start()) {
                return source.substring(had.get(i).end(), had.get(i + 1).start())
                        .indexOf('\n') >= 0;
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

    /** Whether the canonical form wrote the break it writes to separate two items. */
    private static boolean separates(Formatter.CanonicalForm canonical, Place previous, Place next) {
        int from = canonical.layout().extents().get(previous).end();
        int to = canonical.layout().extents().get(next).start();
        for (Newline n : canonical.layout().breaks()) {
            if (n.offset() >= from && n.offset() < to
                    && n.cause() instanceof Newline.Cause.Forced f
                    && f.obligation() == Obligation.A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS) {
                return true;
            }
        }
        return false;
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

    /** Which place each column of the canonical text opens, taking the widest where several begin
     *  together: the line belongs to what holds the rest of it. */
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
