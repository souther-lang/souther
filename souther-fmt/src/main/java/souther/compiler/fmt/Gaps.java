package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;

import java.util.ArrayList;
import java.util.List;

/**
 * Answers every boundary of a {@link TokenDoc} and hands back the {@link Doc} the renderer lays out.
 *
 * <p>Two walks in the same order. The first finds what is written — the tokens, the comments between
 * them, and the boundaries — and asks {@link Spacing#between} about each boundary the layout can
 * leave unbroken. The second builds the document, taking the answers in the order the first made
 * them. Two walks rather than one because a boundary is answered from the token after it as much as
 * from the token before it, and the one after has not been reached when the boundary is.
 *
 * <p>The construct a boundary belongs to is the deepest {@link TokenDoc.Node} holding both of its
 * tokens, and it is found from the tokens rather than from where the boundary was placed. A
 * construct that put the boundary inside one of its members would otherwise be answering as that
 * member, which is a way of deciding the spacing that this is meant to take away.
 */
final class Gaps {

    private Gaps() {
    }

    static Doc resolve(TokenDoc doc) {
        List<Slot> slots = new ArrayList<>();
        collect(doc, null, slots);
        List<String> answers = new ArrayList<>();
        for (int i = 0; i < slots.size(); i++) {
            if (slots.get(i) instanceof GapSlot gap) {
                answers.add(gap.policy() == TokenDoc.Break.ALWAYS
                        ? null : spell(slots, i, gap.policy()));
            }
        }
        return lower(doc, answers, new int[1]);
    }

    /** The construct a token is under, and the ones above that. One of these is built per node
     * entered, so two tokens under one node hold the same instance and the deepest construct
     * holding both is found by walking up rather than by comparing names. */
    private record Within(SyntaxKind kind, Within outer, int depth) {
    }

    /** What the first walk finds, in the order it is written. */
    private sealed interface Slot {
    }

    private record TokenSlot(SyntaxKind kind, Within within) implements Slot {
    }

    /** A comment. It ends the interval a boundary beside it would otherwise hold. */
    private record TriviaSlot() implements Slot {
    }

    private record GapSlot(TokenDoc.Break policy) implements Slot {
    }

    /** One boundary of a document: what the layout may do there, the kind on each side, and the
     * construct that joins them. The construct is null where the boundary always breaks or a
     * comment stands beside it, which are the two the rule is not asked about. */
    record Boundary(TokenDoc.Break policy, SyntaxKind left, SyntaxKind right, SyntaxKind joining) {
    }

    /**
     * Every boundary of {@code doc}, in the order it is written, one for each pair of code tokens
     * it stands between. For a check that has to see what the document decided rather than what it
     * rendered to.
     */
    static List<Boundary> boundaries(TokenDoc doc) {
        List<Slot> slots = new ArrayList<>();
        collect(doc, null, slots);
        List<Boundary> out = new ArrayList<>();
        boolean sinceAToken = true;
        for (int i = 0; i < slots.size(); i++) {
            if (slots.get(i) instanceof TokenSlot) {
                sinceAToken = true;
            }
            if (!(slots.get(i) instanceof GapSlot gap)) {
                continue;
            }
            if (!sinceAToken) {
                // more than one boundary where the tokens have one adjacency: the two breaks of a
                // blank line, and the two just inside brackets that hold nothing but comments
                continue;
            }
            sinceAToken = false;
            // Reported for every boundary, including the ones the rule is not asked about, so that
            // each of them says which two tokens it stands between. Walks past a comment and past
            // another boundary rather than refusing: a blank line is two breaks at one adjacency.
            TokenSlot left = nearestToken(slots, i, -1);
            TokenSlot right = nearestToken(slots, i, 1);
            Within joining = left == null || right == null || crossesAComment(slots, i)
                    ? null : deepestHolding(left.within(), right.within());
            out.add(new Boundary(gap.policy(), left == null ? null : left.kind(),
                    right == null ? null : right.kind(), joining == null ? null : joining.kind()));
        }
        return out;
    }

    private static TokenSlot nearestToken(List<Slot> slots, int i, int step) {
        for (int j = i + step; j >= 0 && j < slots.size(); j += step) {
            if (slots.get(j) instanceof TokenSlot t) {
                return t;
            }
        }
        return null;
    }

    /** Whether a comment stands between the boundary at {@code i} and the token on either side. */
    private static boolean crossesAComment(List<Slot> slots, int i) {
        for (int step : new int[] {-1, 1}) {
            for (int j = i + step; j >= 0 && j < slots.size(); j += step) {
                if (slots.get(j) instanceof TokenSlot) {
                    break;
                }
                if (slots.get(j) instanceof TriviaSlot) {
                    return true;
                }
            }
        }
        return false;
    }

    /** The pairs of code tokens {@code doc} writes next to each other with no boundary between
     * them. A construct that leaves one out is deciding what goes there by leaving it out, so the
     * rule holds everywhere only while this is empty. */
    static List<String> adjacenciesWithNoBoundary(TokenDoc doc) {
        List<Slot> slots = new ArrayList<>();
        collect(doc, null, slots);
        List<String> out = new ArrayList<>();
        TokenSlot previous = null;
        boolean boundarySince = true;
        for (Slot slot : slots) {
            switch (slot) {
                case TokenSlot t -> {
                    if (previous != null && !boundarySince) {
                        out.add(previous.kind() + " " + t.kind());
                    }
                    previous = t;
                    boundarySince = false;
                }
                case GapSlot _ -> boundarySince = true;
                case TriviaSlot _ -> boundarySince = true;
            }
        }
        return out;
    }

    private static void collect(TokenDoc doc, Within within, List<Slot> out) {
        switch (doc) {
            case TokenDoc.Nil _ -> { }
            case TokenDoc.MustBreak _ -> { }
            case TokenDoc.Token t -> out.add(new TokenSlot(t.kind(), within));
            case TokenDoc.Comment _ -> out.add(new TriviaSlot());
            case TokenDoc.Trailing _ -> out.add(new TriviaSlot());
            case TokenDoc.Gap g -> out.add(new GapSlot(g.policy()));
            case TokenDoc.Node n -> collect(n.doc(),
                    new Within(n.kind(), within, within == null ? 0 : within.depth() + 1), out);
            // A place names a position and joins nothing, so the construct a boundary belongs to is
            // found past it: two tokens on either side of a place are joined by whatever holds it.
            case TokenDoc.At a -> collect(a.doc(), within, out);
            case TokenDoc.Carries c -> throw new IllegalStateException(
                    "a carrier reached the layout unresolved (" + c.which() + " of " + c.place()
                            + "); the comments go in before the boundaries are answered");
            case TokenDoc.Vacant v -> throw new IllegalStateException(
                    "brackets reached the layout without being told what is between them ("
                            + v.construct() + ")");
            case TokenDoc.Nest n -> collect(n.doc(), within, out);
            case TokenDoc.Group g -> collect(g.doc(), within, out);
            case TokenDoc.Concat c -> {
                for (TokenDoc part : c.parts()) {
                    collect(part, within, out);
                }
            }
        }
    }

    /**
     * What is written at the boundary at {@code i} where the layout does not break it.
     *
     * <p>Nothing, where a comment stands on either side of it. A comment cannot share the line
     * after it, so a group holding one is never laid out flat and this boundary is one the output
     * always breaks; what it would have held unbroken is not written, and the rule is not asked a
     * question about an interval that is the comment's.
     */
    private static String spell(List<Slot> slots, int i, TokenDoc.Break policy) {
        TokenSlot left = neighbour(slots, i, -1, policy);
        TokenSlot right = neighbour(slots, i, 1, policy);
        if (left == null || right == null) {
            return Spacing.TIGHT;
        }
        Within joining = deepestHolding(left.within(), right.within());
        if (joining == null) {
            throw new IllegalStateException(
                    "no construct holds both " + left.kind() + " and " + right.kind()
                            + "; a boundary belongs to the construct that joins its two tokens");
        }
        return Spacing.between(joining.kind(), left.kind(), right.kind());
    }

    /**
     * The code token on one side of the boundary at {@code i}. There has to be one.
     *
     * <p>Null where a comment stands on that side and the boundary may break, and refused where it
     * may not. A comment cannot share the line after it, so a group holding one is never laid out
     * flat: a boundary that may break and has a comment beside it is one the output always breaks,
     * and the answer this returns for it is never written. A boundary that cannot break has no such
     * answer — the line would go on inside the comment — and a construct that wrote one there is
     * writing something the reader cannot read.
     *
     * <p>Another boundary on that side means a construct wrote two where its tokens have one, which
     * is how {@code exposing (  )} came to hold two spaces.
     */
    private static TokenSlot neighbour(List<Slot> slots, int i, int step, TokenDoc.Break policy) {
        for (int j = i + step; j >= 0 && j < slots.size(); j += step) {
            switch (slots.get(j)) {
                case TokenSlot t -> {
                    return t;
                }
                case TriviaSlot _ -> {
                    if (policy != TokenDoc.Break.MAY) {
                        throw new IllegalStateException(
                                "a comment stands beside a boundary that cannot break; the line"
                                        + " after it would be written inside the comment");
                    }
                    return null;   // the comment's line, and this boundary breaks
                }
                case GapSlot _ -> throw new IllegalStateException(
                        "two boundaries meet where their tokens have one adjacency");
            }
        }
        throw new IllegalStateException(
                "a boundary with no code token on one side; every boundary joins two of them");
    }

    /** The deepest construct holding both tokens, which is the one that joins them. */
    private static Within deepestHolding(Within left, Within right) {
        Within a = left;
        Within b = right;
        while (a != null && b != null && a.depth() > b.depth()) {
            a = a.outer();
        }
        while (a != null && b != null && b.depth() > a.depth()) {
            b = b.outer();
        }
        while (a != null && b != null && a != b) {
            a = a.outer();
            b = b.outer();
        }
        return a == b ? a : null;
    }

    private static Doc lower(TokenDoc doc, List<String> answers, int[] next) {
        return switch (doc) {
            case TokenDoc.Nil _ -> Doc.NIL;
            case TokenDoc.MustBreak _ -> Doc.MUST_BREAK;
            case TokenDoc.Token t -> Doc.text(t.lexeme());
            case TokenDoc.Comment c -> Doc.text(c.text());
            case TokenDoc.Trailing t -> Doc.trailing(t.text());
            case TokenDoc.Node n -> lower(n.doc(), answers, next);
            case TokenDoc.At a -> lower(a.doc(), answers, next);
            case TokenDoc.Carries _, TokenDoc.Vacant _ -> throw new IllegalStateException(
                    "a carrier reached the layout unresolved");
            case TokenDoc.Nest n -> Doc.nest(n.indent(), lower(n.doc(), answers, next));
            case TokenDoc.Group g -> Doc.group(lower(g.doc(), answers, next));
            case TokenDoc.Concat c -> {
                List<Doc> parts = new ArrayList<>();
                for (TokenDoc part : c.parts()) {
                    parts.add(lower(part, answers, next));
                }
                yield Doc.concat(parts);
            }
            case TokenDoc.Gap g -> {
                String flat = answers.get(next[0]++);
                yield switch (g.policy()) {
                    case ALWAYS -> Doc.HARDLINE;
                    case MAY -> flat.isEmpty() ? Doc.SOFTLINE : Doc.LINE;
                    case NEVER -> flat.isEmpty() ? Doc.NIL : Doc.text(flat);
                };
            }
        };
    }
}
