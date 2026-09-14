package souther.compiler.fmt;

import souther.compiler.text.DisplayColumns;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.Iterator;
import java.util.List;

/**
 * A Wadler/Leijen pretty-printing document. A {@link #group} is laid out flat (its {@link #line}s
 * become spaces) when it fits the target width, or broken (its lines become newlines at the current
 * indent) otherwise. This is what lets the formatter keep a short record or pipeline on one line and
 * break a long one, from a single description of its shape.
 */
sealed interface Doc {

    Doc NIL = new Nil();

    /**
     * How many times a document is laid out before every column has settled.
     *
     * <p>A stop is settled by the pass after the one that settled the stop before it on its line,
     * and one more pass sees that nothing moved. So it is one more than the stops there are — read
     * from {@link Columns.Stop} because that is where they are listed, and held here because how
     * many times this lays a document out is this file's and not the rule's.
     */
    int PASSES = Columns.Stop.values().length + 1;

    /** Writes nothing, and the group holding it is never laid out flat. A comment cannot share the
     * line after it, so a construct holding one breaks even where its own content would have fitted
     * — and where the break itself is the enclosing construct's to write, as the brackets of a list
     * whose only content is a comment. */

    record Nil() implements Doc {}
    record Text(String s) implements Doc {}

    /**
     * Which of the things that refuse a flat layout this one is, and the obligation it discharges.
     *
     * <p>An identity because a group is broken by one of them in particular, and told apart only by
     * their kind two hardlines are one answer. The obligation is on it rather than beside it: what
     * refused and why it was written there are one fact, and a layout that carried the first alone
     * would send a reader back to the document to look the second up.
     */
    final class Ref {

        private final Obligation obligation;

        Ref(Obligation obligation) {
            if (obligation == null) {
                throw new IllegalArgumentException(
                        "a break written whatever the width says what it is written for");
            }
            this.obligation = obligation;
        }

        Obligation obligation() {
            return obligation;
        }
    }
    /**
     * A document that cannot be laid out flat, and which says what it is written for.
     *
     * <p>Three of them, and a group broken by one is broken by one of these. Named as a kind so
     * that a broken group can be asked its obligation and answer, rather than the caller matching
     * over three cases that all hold the same thing.
     */
    sealed interface Refuses permits Hard, Trailing, MustBreak {

        Ref ref();

        /** The obligation the group holding this was written down the page for. */
        default Obligation obligation() {
            return ref().obligation();
        }
    }

    record Line(LineRef ref, String flat) implements Doc {}

    /** Which place the layout may break this is. Two written the same way are two of them, and the
     * conditional-layout rule answers about the group that settles one rather than about a kind of
     * boundary. */
    final class LineRef {
    }

    /** A break, the obligation it is written for, and whether it writes the indent of the line it
     *  opens. The one that does not is the one that leaves a blank line: nothing is on that line,
     *  so it has no indent. */
    record Hard(Ref ref, boolean indents) implements Doc, Refuses {}
    record Concat(List<Doc> parts) implements Doc {}
    record Nest(NestRef ref, int indent, Doc doc) implements Doc {}

    /** Which nesting a nesting is. Two written the same way are two of them, and what the
     * indentation rule answers about is a pair of consecutive ones rather than a pair of amounts. */
    final class NestRef {
    }
    record Group(GroupRef ref, Doc doc) implements Doc {}

    /** What is written at one place of the canonical form. The document says which place; the
     * layout says where it ended up. */
    record At(Place place, Doc doc) implements Doc {}

    /** Where a place is, for one that writes nothing of its own. */
    record PointOf(Place place) implements Doc {}

    /**
     * Which group a group is. Two groups written the same way are still two of them, and a layout
     * that kept its decisions by their shape would keep one — so this is an identity and carries
     * nothing else.
     */
    final class GroupRef {
    }

    /**
     * A comment written at the end of a line of code. It is not content the width has to make room
     * for — it sits past the end of the line whatever its length — but nothing else can share the
     * line after it, so a group holding one cannot be laid out flat.
     */
    record Trailing(Ref ref, String s) implements Doc, Refuses {}

    record MustBreak(Ref ref) implements Doc, Refuses {}

    /**
     * A column of a table, at the place one row is written to it. Writes the spaces that carry the
     * connector after it out to the column, and nothing where the row is written down the page.
     *
     * <p>It stands after the boundary rather than in place of it: what separates two tokens is
     * {@link Spacing}'s answer and this never touches it. So a row already at the column has this
     * write nothing, and the text either way holds the separator the rule wrote.
     *
     * <p>What it writes is not measured. See {@link #layout}.
     */
    record ColumnStop(Columns.Unit unit) implements Doc {}

    static Doc text(String s) {
        return new Text(s);
    }

    /** A space when the line it is on is whole, and a newline where it is not. */
    static Doc line() {
        return new Line(new LineRef(), " ");
    }

    /** Nothing when the line it is on is whole, and a newline where it is not. */
    static Doc softline() {
        return new Line(new LineRef(), "");
    }

    /** Always a newline, for the obligation named, and the group holding it is never laid out
     *  flat. */
    static Hard hardline(Obligation obligation) {
        return new Hard(new Ref(obligation), true);
    }

    /** The same, leaving the line it opens empty: a blank line, written with no indent on it. */
    static Hard blankLine(Obligation obligation) {
        return new Hard(new Ref(obligation), false);
    }

    /** Writes nothing, and the group holding it is never laid out flat. What writes one is a
     *  comment on a line of its own, so that is the obligation it discharges. */
    static Doc mustBreak() {
        return new MustBreak(new Ref(Obligation.NOTHING_SHARES_A_COMMENTS_LINE));
    }

    static Doc concat(Doc... parts) {
        return new Concat(List.of(parts));
    }

    static Doc concat(List<Doc> parts) {
        return new Concat(List.copyOf(parts));
    }

    /** A comment at the end of the line the preceding document ends on. Nothing can follow it on
     *  that line, which is the obligation it refuses a flat layout for. */
    static Doc trailing(String s) {
        return new Trailing(new Ref(Obligation.NOTHING_SHARES_A_COMMENTS_LINE), s);
    }

    static Doc nest(int indent, Doc doc) {
        return new Nest(new NestRef(), indent, doc);
    }

    /** The place one row of a table is written out to one of its columns. */
    static Doc columnStop(Columns.Unit unit) {
        return new ColumnStop(unit);
    }

    static Doc at(Place place, Doc doc) {
        return new At(place, doc);
    }

    static Doc pointOf(Place place) {
        return new PointOf(place);
    }

    static Doc group(Doc doc) {
        return new Group(new GroupRef(), doc);
    }

    /** Joins {@code parts} with {@code sep} between each. */
    static Doc join(Doc sep, List<Doc> parts) {
        List<Doc> out = new ArrayList<>();
        for (int i = 0; i < parts.size(); i++) {
            if (i > 0) {
                out.add(sep);
            }
            out.add(parts.get(i));
        }
        return new Concat(out);
    }

    /** The text this document lays out to at the given target {@code width} (columns), which is
     * {@link #layout}'s projection. */
    default String render(int width) {
        return layout(width).text();
    }

    /**
     * This document laid out at the given target {@code width} (columns): the text, and what the
     * layout decided on the way to it.
     *
     * <p>A decision is taken once, where the outer walk reaches the group. The fitting walk goes ahead
     * over groups it is only measuring and takes none, so what comes back is what was laid out
     * rather than what was considered.
     *
     * <p>A column cannot be decided that way. Where a row's connector goes depends on every other
     * row of its table, and the walk that reaches the first row has not read the last one — so the
     * document is laid out, the columns are read off what that wrote, and it is laid out again to
     * write them. The alternative is to look ahead over the table at the row that opens it, which
     * would be a second walk deciding what the real one has to decide again; the same machine run
     * twice cannot disagree with itself.
     *
     * <p>It settles because a column depends only on the columns before it on its line: the first
     * stop is settled by the first pass, the one after it by the second, and one more pass sees that
     * nothing moved. {@link #PASSES} is that count and this refuses to run past it.
     *
     * <p>A document with no table is laid out once. The first pass writes no stop, so there is
     * nothing to settle and the layout it produced is the answer — which is what keeps this off the
     * files that have no columns in them.
     */
    default Layout layout(int width) {
        java.util.Map<Columns.Unit, Integer> columns = java.util.Map.of();
        for (int pass = 0; ; pass++) {
            Layout laid = laidOut(width, columns);
            java.util.Map<Columns.Unit, Integer> settled = settle(laid.stops());
            if (settled.equals(columns)) {
                return laid;
            }
            if (pass >= PASSES) {
                throw new IllegalStateException(
                        "the columns of a table did not settle in " + PASSES
                                + " layouts; a column reads the ones before it on its line and"
                                + " nothing else, so this is a cycle that should not exist");
            }
            columns = settled;
        }
    }

    /**
     * Where each column is, from what the rows reached without it. The greatest natural column, so
     * that the row that needed the most room is the one the rule writes nothing for.
     */
    private static java.util.Map<Columns.Unit, Integer> settle(List<ColumnOccurrence> stops) {
        java.util.Map<Columns.Unit, Integer> out = new java.util.LinkedHashMap<>();
        for (ColumnOccurrence stop : stops) {
            out.merge(stop.unit(), stop.naturalColumn(), Math::max);
        }
        return out;
    }

    /** One layout, writing the columns it is given. */
    private Layout laidOut(int width, java.util.Map<Columns.Unit, Integer> columns) {
        List<GroupDecision> decisions = new ArrayList<>();
        List<Newline> breaks = new ArrayList<>();
        List<Opportunity> opportunities = new ArrayList<>();
        List<ColumnOccurrence> stops = new ArrayList<>();
        java.util.Map<Place, Extent> extents = new java.util.LinkedHashMap<>();
        // A place that writes a region and also carries a comment has both an `At` and a
        // point; the region is where it is, so the points are kept apart and read only
        // for the places no region located.
        java.util.Map<Place, Extent> points = new java.util.LinkedHashMap<>();
        java.util.Map<Place, Integer> opened = new java.util.IdentityHashMap<>();
        StringBuilder sb = new StringBuilder();
        Deque<Item> todo = new ArrayDeque<>();
        todo.push(new Item(0, Mode.BREAK, this));   // the outermost context breaks
        // Three counts run side by side here and no two of them are interchangeable. Everything
        // taken from `sb.length()` — an extent, an opportunity, a newline's offset — is an index
        // into the text, which is what the readers of a layout use to cut and search the same Java
        // string, and stays in UTF-16 units. The other two are columns on the screen, which is what
        // a full-width character advances by two and what a tab advances to the next multiple of
        // eight of.
        //
        // `measuredCol` is what the width reads, and a table's padding is not in it: a group whose
        // flatness depended on padding would be decided by a column that is decided by which rows
        // came out flat. `writtenCol` is where the line has actually reached, padding and all, and
        // it is what a column is settled in — a row's second connector stands where its first one
        // pushed it to.
        //
        // Two counts and not one with a correction added to it. How far a token advances a column
        // depends on the column it starts at, which is the whole of what a tab is; a written column
        // reconstructed as `measuredCol` plus the padding so far is right for every token but that
        // one, and wrong for the rows of a table that holds it.
        int measuredCol = 0;
        int writtenCol = 0;
        while (!todo.isEmpty()) {
            Item it = todo.pop();
            if (it.closes != null) {
                extents.put(it.closes, new Extent(opened.get(it.closes), sb.length()));
                continue;
            }
            switch (it.doc) {
                case Nil _ -> { }
                case Text t -> {
                    sb.append(t.s());
                    measuredCol = DisplayColumns.advance(t.s(), measuredCol);
                    writtenCol = DisplayColumns.advance(t.s(), writtenCol);
                }
                case Concat c -> {
                    List<Doc> parts = c.parts();
                    for (int i = parts.size() - 1; i >= 0; i--) {
                        todo.push(it.within(parts.get(i)));
                    }
                }
                case Nest n -> todo.push(new Item(it.indent + n.indent(), it.mode, n.doc(), null,
                        new Nesting(n.ref(), it.under), it.within()));
                case PointOf p -> points.putIfAbsent(p.place(),
                        new Extent(sb.length(), sb.length()));
                case At a -> {
                    // The close is pushed first so that it is popped after everything written at
                    // the place, which is what makes the span the interval the place occupies.
                    opened.put(a.place(), sb.length());
                    todo.push(new Item(it.indent, it.mode, Doc.NIL, a.place(), it.under,
                            it.within()));
                    todo.push(it.within(a.doc()));
                }
                case Group g -> {
                    Outcome outcome = flatnessOf(measuredCol, width,
                            new Item(it.indent, Mode.FLAT, g.doc()), todo);
                    decisions.add(new GroupDecision(g.ref(), measuredCol, outcome));
                    todo.push(new Item(it.indent,
                            outcome instanceof Outcome.Flat ? Mode.FLAT : Mode.BREAK, g.doc(),
                            null, it.under, g.ref()));
                }
                case Line l -> {
                    // The group that settles it is the innermost one holding it, which is the one
                    // the walk was inside when it reached here. One outside every group is not an
                    // opportunity: the outermost context breaks, so it always breaks and no
                    // decision settles it. The formatter writes none, which is its own check.
                    if (it.within() != null) {
                        opportunities.add(new Opportunity(l.ref(), it.within(),
                                it.mode != Mode.FLAT, sb.length()));
                    }
                    if (it.mode == Mode.FLAT) {
                        sb.append(l.flat());
                        measuredCol = DisplayColumns.advance(l.flat(), measuredCol);
                        writtenCol = DisplayColumns.advance(l.flat(), writtenCol);
                    } else {
                        breaks.add(newline(sb, it, it.indent,
                                new Newline.Cause.Settled(l.ref()), true));
                        measuredCol = it.indent;
                        writtenCol = it.indent;
                    }
                }
                case Hard h -> {
                    int indent = h.indents() ? it.indent : 0;
                    breaks.add(newline(sb, it, indent,
                            new Newline.Cause.Forced(h.ref().obligation()), h.indents()));
                    measuredCol = indent;
                    writtenCol = indent;
                }
                case Trailing t -> {
                    sb.append(' ').append(t.s());
                    measuredCol = DisplayColumns.advance(t.s(), measuredCol + 1);
                    writtenCol = DisplayColumns.advance(t.s(), writtenCol + 1);
                }
                case MustBreak _ -> { }
                case ColumnStop cs -> {
                    // A row written down the page has its connector opening a line, and there is no
                    // column to be at there. It neither reaches for one nor says how wide it is.
                    if (it.mode == Mode.FLAT) {
                        Integer column = columns.get(cs.unit());
                        // Nothing to write on the pass that is finding out where the column is, and
                        // nothing on a pass whose column is one an earlier pass measured short. The
                        // pass after it has the room this one asked for.
                        int pad = column == null ? 0 : Math.max(0, column - writtenCol);
                        stops.add(new ColumnOccurrence(cs.unit(), sb.length(), writtenCol));
                        sb.append(" ".repeat(pad));
                        // What the width reads is untouched, which is the whole of the rule.
                        writtenCol += pad;
                    }
                }
            }
        }
        points.forEach(extents::putIfAbsent);
        List<ColumnDecision> settled = new ArrayList<>();
        columns.forEach((unit, column) -> settled.add(new ColumnDecision(unit, column)));
        return new Layout(sb.toString(), decisions, extents, breaks, opportunities, settled, stops);
    }

    /** Writes a break and says what it wrote, and what wrote it. {@code indent} is the item's,
     *  except on the break that leaves a blank line, whose line has nothing on it to indent. */
    private static Newline newline(StringBuilder sb, Item it, int indent, Newline.Cause cause,
            boolean indents) {
        int offset = sb.length();
        sb.append('\n').append(" ".repeat(indent));
        return new Newline(offset, indent,
                it.under() == null ? List.of() : it.under().outermostFirst(), cause, indents);
    }

    /**
     * What a flat layout of a group comes to: written on one line, or written down the page because
     * it is over the width, or because something in it refuses to share a line at all.
     *
     * <p>Refusing wins over the width. A group holding a forced break is written down the page
     * whatever it is measured against, so the width did not decide it — and answering with whichever
     * of the two the walk met first would make the reason a fact about where the measuring stopped.
     * The walk therefore goes on past the overflow, over the group's own flat content, to see
     * whether one is there.
     *
     * <p>It walks forward from {@code from}, the column the group begins at, rather than spending a
     * budget of what is left of the width. The two are the same arithmetic until a tab is written:
     * a tab advances to the next stop, which is decided by the absolute column it stands at and
     * cannot be recovered from how much of the width remains. A comment or a string literal carries
     * one through to here as it was written, so this is not a case the formatter can rule out.
     */
    private static Outcome flatnessOf(int from, int limit, Item first, Deque<Item> rest) {
        int displayCol = from;
        boolean over = displayCol > limit;
        Deque<Item> todo = new ArrayDeque<>();
        todo.push(first);
        Iterator<Item> restIt = rest.iterator();
        while (true) {
            Item it;
            if (!todo.isEmpty()) {
                it = todo.pop();
            } else if (restIt.hasNext()) {
                it = restIt.next();
            } else {
                return over ? new Outcome.BrokenByWidth() : new Outcome.Flat();
            }
            switch (it.doc) {
                case Nil _ -> { }
                case Text t -> {
                    displayCol = DisplayColumns.advance(t.s(), displayCol);
                    over |= displayCol > limit;
                }
                case Concat c -> {
                    List<Doc> parts = c.parts();
                    for (int i = parts.size() - 1; i >= 0; i--) {
                        todo.push(new Item(it.indent, it.mode, parts.get(i)));
                    }
                }
                case Nest n -> todo.push(new Item(it.indent + n.indent(), it.mode, n.doc()));
                case Group g -> todo.push(new Item(it.indent, it.mode, g.doc()));
                case At a -> todo.push(new Item(it.indent, it.mode, a.doc()));
                case PointOf _ -> { }
                case Line l -> {
                    if (it.mode == Mode.FLAT) {
                        displayCol = DisplayColumns.advance(l.flat(), displayCol);
                        over |= displayCol > limit;
                    } else {
                        // the measured stretch ends here, and what follows is another line's
                        return over ? new Outcome.BrokenByWidth() : new Outcome.Flat();
                    }
                }
                // Refuses a flat layout where it is inside the group being measured. In an
                // already-broken outer context it just ends the stretch being measured.
                case Hard h -> {
                    if (it.mode == Mode.FLAT) {
                        return new Outcome.BrokenByForcedLayout(h);
                    }
                    return over ? new Outcome.BrokenByWidth() : new Outcome.Flat();
                }
                case Trailing t -> {
                    if (it.mode == Mode.FLAT) {
                        return new Outcome.BrokenByForcedLayout(t);
                    }
                    return over ? new Outcome.BrokenByWidth() : new Outcome.Flat();
                }
                case MustBreak m -> {
                    if (it.mode == Mode.FLAT) {
                        return new Outcome.BrokenByForcedLayout(m);
                    }
                    return over ? new Outcome.BrokenByWidth() : new Outcome.Flat();
                }
                // Padding is not content the width has to make room for, the same as a trailing
                // comment is not. What it writes is read off a column, and a column that a group's
                // flatness read would be decided by the rows that came out flat.
                case ColumnStop _ -> { }
            }
        }
    }

    enum Mode { FLAT, BREAK }

    /** {@code closes} is the place this item ends, and is set only on the marker pushed to run
     * after everything written at that place. {@code under} is the nestings it is written inside,
     * innermost first. */
    record Item(int indent, Mode mode, Doc doc, Place closes, Nesting under, GroupRef within) {

        Item(int indent, Mode mode, Doc doc) {
            this(indent, mode, doc, null, null, null);
        }

        Item(int indent, Mode mode, Doc doc, Place closes) {
            this(indent, mode, doc, closes, null, null);
        }

        Item(int indent, Mode mode, Doc doc, Place closes, Nesting under) {
            this(indent, mode, doc, closes, under, null);
        }

        Item within(Doc doc) {
            return new Item(indent, mode, doc, null, under, within);
        }
    }

    /** The nestings something is written inside, innermost first. */
    record Nesting(NestRef ref, Nesting outer) {

        /** Outermost first, which is the order the levels are read in. */
        List<NestRef> outermostFirst() {
            List<NestRef> out = new ArrayList<>();
            for (Nesting n = this; n != null; n = n.outer()) {
                out.add(0, n.ref());
            }
            return out;
        }
    }
}
