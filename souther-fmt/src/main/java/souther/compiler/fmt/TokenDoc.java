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
 * ten pairs is that name.
 *
 * <p>There is no way to build a leaf holding more than one token, or holding the interval between
 * two. That is what closes the arrangement issue #476 describes: a construct cannot spell a
 * separator even by accident, because there is nothing here to spell one with.
 */
sealed interface TokenDoc {

    TokenDoc NIL = new Nil();

    /** Two tokens on one line, with whatever the rule says between them. */
    TokenDoc GAP = new Gap(Break.NEVER, null, true);

    /** A boundary the layout may break, and which holds the rule's answer where it does not. */
    TokenDoc SOFT_GAP = new Gap(Break.MAY, null, true);

    /** Writes nothing, and the group holding it is never laid out flat — {@link Doc.MustBreak}.
     *  What refuses is a comment, so it is that obligation this discharges. */
    TokenDoc MUST_BREAK = new MustBreak(Obligation.NOTHING_SHARES_A_COMMENTS_LINE);

    /** A boundary the layout always breaks, and the obligation it is written for. It has no
     *  unbroken form, so the spacing rule is not asked about it — and there is no constant for one,
     *  because a forced boundary with no obligation would be the policy standing in for the rule
     *  again. */
    static TokenDoc forced(Obligation obligation) {
        return new Gap(Break.ALWAYS, obligation, true);
    }

    /** A break that leaves a line with nothing on it, which is what a blank line is. Written before
     *  the boundary that opens the next line, so the two together are one blank line. */
    static TokenDoc blank(Obligation obligation) {
        return new Gap(Break.ALWAYS, obligation, false);
    }

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

    /**
     * Where in the canonical form this document is written, and what opens the line it is on.
     *
     * <p>A {@link Node} names what joins two tokens and is asked of the spacing rule; this names a
     * position and is asked of nothing. It is what comment ownership addresses when it says which
     * construct can carry a comment — a question a {@code Node} cannot answer, since two siblings
     * written as the same kind of construct are one {@code Node} kind and two places.
     */
    record At(Place place, TokenDoc doc) implements TokenDoc {}

    /**
     * Where the comments a place carries in one direction are written.
     *
     * <p>A construct leaves the slot and says nothing about what goes in it. What does is decided
     * once every place exists — which is after the construction and before the layout, because a
     * comment cannot share the line after it and so decides whether the group holding it can be laid
     * out flat. A construct that settled it here would be answering from the source tree, which is
     * the structure the canonical form is not.
     */
    record Carries(Place place, Carrier which) implements TokenDoc {}

    /**
     * Where a place is, for a place that writes nothing of its own. A place naming the line a
     * construct opens with carries the comment written at the end of it and emits no text, so it
     * has a position and no region — and this says the position rather than claiming the place
     * wrote something, which is what an {@link At} says.
     */
    record PointOf(Place place) implements TokenDoc {}

    /**
     * Brackets with no member written between them.
     *
     * <p>What goes there is one line or none, and which of the two depends on whether the place was
     * handed any comments — a construct with nothing in it is written {@code ()}, and one holding
     * only a comment keeps the line the comment is on. The construction does not know which, so it
     * hands over the brackets and lets the same pass that answers the carriers say.
     */
    record Vacant(Place place, SyntaxKind construct, TokenDoc open, TokenDoc close, int indent)
            implements TokenDoc {}

    /**
    /**
     * A boundary, the obligation it is written for where it always breaks, and whether the break it
     * may write indents the line it opens.
     *
     * <p>The obligation is there exactly where the policy is {@link Break#ALWAYS}. A boundary the
     * layout may break is settled by the group holding it and a boundary it may not is the spacing
     * rule's, so those two say which rule answers them by their policy alone; a forced one does
     * not, and five constructions write one.
     *
     * <p>Every boundary but one indents. The exception is the break that leaves a blank line: the
     * line it opens has nothing on it, so it has no indent to write, and writing one would leave
     * spaces on a line a reader sees as empty and an editor strips.
     */
    record Gap(Break policy, Obligation forced, boolean indents) implements TokenDoc {

        public Gap {
            if ((policy == Break.ALWAYS) != (forced != null)) {
                throw new IllegalArgumentException(
                        "a forced boundary says what forced it, and no other boundary does: "
                                + policy + " with " + forced);
            }
        }
    }

    record Concat(List<TokenDoc> parts) implements TokenDoc {}

    record Nest(int indent, TokenDoc doc) implements TokenDoc {}

    record Group(TokenDoc doc) implements TokenDoc {}

    /** Writes nothing and refuses a flat layout, for the obligation named. */
    record MustBreak(Obligation forced) implements TokenDoc {}

    static TokenDoc token(SyntaxKind kind, String lexeme) {
        return new Token(kind, lexeme);
    }

    static TokenDoc node(SyntaxKind kind, TokenDoc doc) {
        return new Node(kind, doc);
    }

    /**
     * {@code doc} at {@code place}, behind whatever opens the line that place is written on, with
     * {@code leading} at the head of that line.
     *
     * <p>The boundary and the place are written together because they are one decision: what stands
     * in front of a place and whether the place has a line of its own to be written above are the
     * same fact, and a construct able to write one without the other is one where the two can
     * disagree.
     */
    static TokenDoc at(Place place, TokenDoc doc) {
        Opening opening = place.opening();
        TokenDoc written = concat(opening.boundary(), new Carries(place, Carrier.ABOVE),
                opening.opener(), new At(place, doc));
        // A place with a line of its own can be written below as well as above, and the slot is
        // outside the place because what is written below it is not part of it. A place the
        // construct runs into has no such line: a comment there would have the rest of the line
        // written inside it, which is the same reason it cannot be written above one.
        return opening.opensALine()
                ? concat(written, new Carries(place, Carrier.BELOW))
                : written;
    }

    /** What the place carries at the end of the line it ends. Written where the construct holding
     *  it has finished writing that line, which is not always straight after the place. */
    static TokenDoc pointOf(Place place) {
        return new PointOf(place);
    }

    static TokenDoc endsTheLineOf(Place place) {
        return new Carries(place, Carrier.TRAILING);
    }

    static TokenDoc carries(Place place, Carrier which) {
        return new Carries(place, which);
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

    /** Joins {@code parts} with {@code sep} between each. */
    static TokenDoc join(TokenDoc sep, List<TokenDoc> parts) {
        List<TokenDoc> out = new java.util.ArrayList<>();
        for (int i = 0; i < parts.size(); i++) {
            if (i > 0) {
                out.add(sep);
            }
            out.add(parts.get(i));
        }
        return new Concat(out);
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
