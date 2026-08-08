package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;

import java.util.List;

/**
 * A document that still holds its tokens, and holds the boundary between two of them as a thing
 * rather than as characters someone already chose. It is what a construct builds; {@link #resolve()}
 * turns it into the {@link Doc} the renderer lays out, and that is the only direction.
 *
 * <p>The point of it is that no construct spells what goes between two tokens. A construct hands
 * over the tokens it writes, says of each boundary whether the layout may break there, and stops.
 * What an unbroken boundary holds is {@link Spacing#between}'s answer and nowhere else's, which is
 * what makes the spacing rule a function instead of the by-product of whichever literal a construct
 * happened to spell (issue #476).
 *
 * <p>So a boundary exists at <em>every</em> adjacency of two code tokens, including the ones written
 * tight. A construct free to leave one out would be deciding by leaving it out, and the rule would
 * hold site by site rather than everywhere.
 *
 * <p>A {@link Node} names the construct that joins what is under it, and it names it as the
 * canonical form writes it rather than as the source had it — see {@link Spacing}, whose answer for
 * nine pairs is that name.
 */
sealed interface TokenDoc {

    TokenDoc NIL = new Nil();

    /** Two tokens on one line, with whatever the rule says between them. */
    TokenDoc GAP = new Gap(Break.NEVER);

    /** A boundary the layout may break, and which holds the rule's answer where it does not. */
    TokenDoc SOFT_GAP = new Gap(Break.MAY);

    /** A boundary the layout always breaks. It has no unbroken form, so the rule is not asked. */
    TokenDoc HARD_GAP = new Gap(Break.ALWAYS);

    /** Writes nothing, and the group holding it is never laid out flat — {@link Doc#MUST_BREAK}. */
    TokenDoc MUST_BREAK = new MustBreak();

    /** What the layout may do at a boundary. What is written where it does not break is not here:
     * that is the rule's, and a construct choosing both would be spelling the separator again. */
    enum Break { NEVER, MAY, ALWAYS }

    record Nil() implements TokenDoc {}

    /** One code token of the canonical form: the kind the rule reads, and the text written. */
    record Token(SyntaxKind kind, String lexeme) implements TokenDoc {}

    /** A comment written on a line of its own. Trivia: it is never an end of a boundary, and a
     * boundary standing beside one always breaks, so no rule is asked about that interval. */
    record Comment(String text) implements TokenDoc {}

    /** A comment written at the end of the line the preceding document ends on. */
    record Trailing(String text) implements TokenDoc {}

    /** The construct joining what is under it, named as the canonical form writes it. */
    record Node(SyntaxKind kind, TokenDoc doc) implements TokenDoc {}

    record Gap(Break policy) implements TokenDoc {}

    record Concat(List<TokenDoc> parts) implements TokenDoc {}

    record Nest(int indent, TokenDoc doc) implements TokenDoc {}

    record Group(TokenDoc doc) implements TokenDoc {}

    record MustBreak() implements TokenDoc {}

    static TokenDoc token(SyntaxKind kind, String lexeme) {
        return new Token(kind, lexeme);
    }

    static TokenDoc node(SyntaxKind kind, TokenDoc doc) {
        return new Node(kind, doc);
    }

    static TokenDoc comment(String text) {
        return new Comment(text);
    }

    static TokenDoc trailing(String text) {
        return new Trailing(text);
    }

    static TokenDoc concat(TokenDoc... parts) {
        return new Concat(List.of(parts));
    }

    static TokenDoc concat(List<TokenDoc> parts) {
        return new Concat(List.copyOf(parts));
    }

    static TokenDoc nest(int indent, TokenDoc doc) {
        return new Nest(indent, doc);
    }

    static TokenDoc group(TokenDoc doc) {
        return new Group(doc);
    }

    /**
     * This document with every boundary answered, as the document the renderer lays out. Answering
     * is a pass of its own and not something the renderer does, so that no layout decision reaches
     * the rule and no spacing decision reaches the renderer.
     */
    default Doc resolve() {
        return Gaps.resolve(this);
    }
}
