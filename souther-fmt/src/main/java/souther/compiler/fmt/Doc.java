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
    Doc HARDLINE = new Hard();       // always a newline; forces the enclosing group to break

    /** Writes nothing, and the group holding it is never laid out flat. A comment cannot share the
     * line after it, so a construct holding one breaks even where its own content would have fitted
     * — and where the break itself is the enclosing construct's to write, as the brackets of a list
     * whose only content is a comment. */
    Doc MUST_BREAK = new MustBreak();

    record Nil() implements Doc {}
    record Text(String s) implements Doc {}
    record Line(String flat) implements Doc {}
    record Hard() implements Doc {}
    record Concat(List<Doc> parts) implements Doc {}
    record Nest(int indent, Doc doc) implements Doc {}
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
    record Trailing(String s) implements Doc {}

    record MustBreak() implements Doc {}

    static Doc text(String s) {
        return new Text(s);
    }

    static Doc concat(Doc... parts) {
        return new Concat(List.of(parts));
    }

    static Doc concat(List<Doc> parts) {
        return new Concat(List.copyOf(parts));
    }

    /** A comment at the end of the line the preceding document ends on. */
    static Doc trailing(String s) {
        return new Trailing(s);
    }

    static Doc nest(int indent, Doc doc) {
        return new Nest(indent, doc);
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
                        todo.push(new Item(it.indent, it.mode, parts.get(i)));
                    }
                }
                case Nest n -> todo.push(new Item(it.indent + n.indent(), it.mode, n.doc()));
                case At a -> {
                    // The close is pushed first so that it is popped after everything written at
                    // the place, which is what makes the span the interval the place occupies.
                    opened.put(a.place(), sb.length());
                    todo.push(new Item(it.indent, it.mode, Doc.NIL, a.place()));
                    todo.push(new Item(it.indent, it.mode, a.doc()));
                }
                case Group g -> {
                    Fit fit = fits(width - col, new Item(it.indent, Mode.FLAT, g.doc()), todo);
                    decisions.add(new GroupDecision(g.ref(), col, switch (fit) {
                        case FITS -> new Outcome.Flat();
                        case TOO_WIDE -> new Outcome.BrokenByWidth();
                        case REFUSED -> new Outcome.BrokenByForcedLayout();
                    }));
                    todo.push(new Item(it.indent,
                            fit == Fit.FITS ? Mode.FLAT : Mode.BREAK, g.doc()));
                }
                case Line l -> {
                    if (it.mode == Mode.FLAT) {
                        sb.append(l.flat());
                        col += l.flat().length();
                    } else {
                        sb.append('\n').append(" ".repeat(it.indent));
                        col = it.indent;
                    }
                }
                case Hard _ -> {
                    sb.append('\n').append(" ".repeat(it.indent));
                    col = it.indent;
                }
                case Trailing t -> {
                    sb.append(' ').append(t.s());
                    col += t.s().length() + 1;
                }
                case MustBreak _ -> { }
            }
        }
        return new Layout(sb.toString(), decisions, spans);
    }

    /** What a flat layout of a group came to. Refused and too wide are not one answer: the first is
     * a fact about the group's content and the second about the width it was measured against. */
    enum Fit { FITS, TOO_WIDE, REFUSED }

    /** Whether the documents starting with {@code first} then the queued rest fit in {@code remaining}
     * columns before the next forced break — the standard flat-fits check. */
    private static Fit fits(int remaining, Item first, Deque<Item> rest) {
        if (remaining < 0) {
            return Fit.TOO_WIDE;
        }
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
                return Fit.FITS;
            }
            switch (it.doc) {
                case Nil _ -> { }
                case Text t -> {
                    remaining -= t.s().length();
                    if (remaining < 0) {
                        return Fit.TOO_WIDE;
                    }
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
                        if (remaining < 0) {
                            return Fit.TOO_WIDE;
                        }
                    } else {
                        return Fit.FITS;   // a break within reach means it fits
                    }
                }
                case Hard _ -> {
                    // a hardline cannot be laid out flat: inside the group under test (FLAT) it forces
                    // a break; in an already-broken outer context it just ends the measured line.
                    return it.mode == Mode.FLAT ? Fit.REFUSED : Fit.FITS;
                }
                case Trailing _ -> {
                    // the same, and for the same reason: whatever follows starts a new line, so it
                    // is measured against that line rather than this one, and the comment's own
                    // width is measured against nothing.
                    return it.mode == Mode.FLAT ? Fit.REFUSED : Fit.FITS;
                }
                case MustBreak _ -> {
                    return it.mode == Mode.FLAT ? Fit.REFUSED : Fit.FITS;
                }
            }
        }
    }

    enum Mode { FLAT, BREAK }

    /** {@code closes} is the place this item ends, and is set only on the marker pushed to run
     * after everything written at that place. */
    record Item(int indent, Mode mode, Doc doc, Place closes) {

        Item(int indent, Mode mode, Doc doc) {
            this(indent, mode, doc, null);
        }
    }
}
