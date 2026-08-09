package souther.compiler.fmt;

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
    Doc LINE = new Line(" ");        // a space when flat, a newline when broken
    Doc SOFTLINE = new Line("");     // nothing when flat, a newline when broken

    /** Writes nothing, and the group holding it is never laid out flat. A comment cannot share the
     * line after it, so a construct holding one breaks even where its own content would have fitted
     * — and where the break itself is the enclosing construct's to write, as the brackets of a list
     * whose only content is a comment. */

    record Nil() implements Doc {}
    record Text(String s) implements Doc {}

    /** Which of the things that refuse a flat layout this one is. A group is broken by one of them
     * in particular, and told apart only by their kind two hardlines are one answer. */
    final class Ref {
    }
    record Line(String flat) implements Doc {}
    record Hard(Ref ref) implements Doc {}
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
    record Trailing(Ref ref, String s) implements Doc {}

    record MustBreak(Ref ref) implements Doc {}

    static Doc text(String s) {
        return new Text(s);
    }

    /** Always a newline, and the group holding it is never laid out flat. */
    static Doc hardline() {
        return new Hard(new Ref());
    }

    /** Writes nothing, and the group holding it is never laid out flat. */
    static Doc mustBreak() {
        return new MustBreak(new Ref());
    }

    static Doc concat(Doc... parts) {
        return new Concat(List.of(parts));
    }

    static Doc concat(List<Doc> parts) {
        return new Concat(List.copyOf(parts));
    }

    /** A comment at the end of the line the preceding document ends on. */
    static Doc trailing(String s) {
        return new Trailing(new Ref(), s);
    }

    static Doc nest(int indent, Doc doc) {
        return new Nest(new NestRef(), indent, doc);
    }

    static Doc at(Place place, Doc doc) {
        return new At(place, doc);
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
     * <p>A decision is taken once, where the outer walk reaches the group. {@link #fits} walks ahead
     * over groups it is only measuring and takes none, so what comes back is what was laid out
     * rather than what was considered.
     */
    default Layout layout(int width) {
        List<GroupDecision> decisions = new ArrayList<>();
        List<Newline> breaks = new ArrayList<>();
        java.util.Map<Place, Span> spans = new java.util.LinkedHashMap<>();
        java.util.Map<Place, Integer> opened = new java.util.IdentityHashMap<>();
        StringBuilder sb = new StringBuilder();
        Deque<Item> todo = new ArrayDeque<>();
        todo.push(new Item(0, Mode.BREAK, this));   // the outermost context breaks
        int col = 0;
        while (!todo.isEmpty()) {
            Item it = todo.pop();
            if (it.closes != null) {
                spans.put(it.closes, new Span(opened.get(it.closes), sb.length()));
                continue;
            }
            switch (it.doc) {
                case Nil _ -> { }
                case Text t -> {
                    sb.append(t.s());
                    col += t.s().length();
                }
                case Concat c -> {
                    List<Doc> parts = c.parts();
                    for (int i = parts.size() - 1; i >= 0; i--) {
                        todo.push(new Item(it.indent, it.mode, parts.get(i), null, it.under));
                    }
                }
                case Nest n -> todo.push(new Item(it.indent + n.indent(), it.mode, n.doc(), null,
                        new Nesting(n.ref(), it.under)));
                case At a -> {
                    // The close is pushed first so that it is popped after everything written at
                    // the place, which is what makes the span the interval the place occupies.
                    opened.put(a.place(), sb.length());
                    todo.push(new Item(it.indent, it.mode, Doc.NIL, a.place(), it.under));
                    todo.push(new Item(it.indent, it.mode, a.doc(), null, it.under));
                }
                case Group g -> {
                    Outcome outcome = flatnessOf(width - col,
                            new Item(it.indent, Mode.FLAT, g.doc()), todo);
                    decisions.add(new GroupDecision(g.ref(), col, outcome));
                    todo.push(new Item(it.indent,
                            outcome instanceof Outcome.Flat ? Mode.FLAT : Mode.BREAK, g.doc(),
                            null, it.under));
                }
                case Line l -> {
                    if (it.mode == Mode.FLAT) {
                        sb.append(l.flat());
                        col += l.flat().length();
                    } else {
                        breaks.add(newline(sb, it));
                        col = it.indent;
                    }
                }
                case Hard _ -> {
                    breaks.add(newline(sb, it));
                    col = it.indent;
                }
                case Trailing t -> {
                    sb.append(' ').append(t.s());
                    col += t.s().length() + 1;
                }
                case MustBreak _ -> { }
            }
        }
        return new Layout(sb.toString(), decisions, spans, breaks);
    }

    /** Writes a break and says what it wrote. */
    private static Newline newline(StringBuilder sb, Item it) {
        int offset = sb.length();
        sb.append('\n').append(" ".repeat(it.indent()));
        return new Newline(offset, it.indent(),
                it.under() == null ? List.of() : it.under().outermostFirst());
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
     */
    private static Outcome flatnessOf(int remaining, Item first, Deque<Item> rest) {
        boolean over = remaining < 0;
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
                    remaining -= t.s().length();
                    over |= remaining < 0;
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
                case Line l -> {
                    if (it.mode == Mode.FLAT) {
                        remaining -= l.flat().length();
                        over |= remaining < 0;
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
            }
        }
    }

    enum Mode { FLAT, BREAK }

    /** {@code closes} is the place this item ends, and is set only on the marker pushed to run
     * after everything written at that place. {@code under} is the nestings it is written inside,
     * innermost first. */
    record Item(int indent, Mode mode, Doc doc, Place closes, Nesting under) {

        Item(int indent, Mode mode, Doc doc) {
            this(indent, mode, doc, null, null);
        }

        Item(int indent, Mode mode, Doc doc, Place closes) {
            this(indent, mode, doc, closes, null);
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
