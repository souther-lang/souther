package souther.compiler.fmt;

import java.util.ArrayList;
import java.util.List;

/**
 * Puts a file's comments into the document, at the places that carry them.
 *
 * <p>It runs between the construction and the layout. After the construction because that is what
 * makes the places, and a comment is filed against a place of the canonical form rather than against
 * a construct of the source — where the two structures differ the source answers about something the
 * canonical form does not write. Before the layout because a comment cannot share the line after it,
 * so which place owns one decides whether the group holding it can be laid out flat.
 *
 * <p>The same shape {@link Gaps} has: the construction leaves a question at each slot, one place
 * answers all of them, and the document handed on has only answered slots in it.
 */
final class Carriers {

    private Carriers() {
    }

    /** What the places were handed. One implementation answers every slot of a document. */
    interface Held {

        /** The comments {@code place} carries in that direction, as documents. A comment is taken
         *  once, so a place asked for one another place has already been given gets nothing. */
        List<TokenDoc> at(Place place, Carrier which);
    }

    /** What the construction left room for. */
    interface Slot {
        void found(Place place, Carrier which);
    }

    /** Every carrier slot {@code doc} holds, in the order it is written. What a place can be handed
     *  is what the construction left room for, so it is read from the document rather than
     *  declared beside it. */
    static void slots(TokenDoc doc, Slot into) {
        switch (doc) {
            case TokenDoc.Carries c -> into.found(c.place(), c.which());
            case TokenDoc.PointOf _ -> { }
            case TokenDoc.Vacant v -> into.found(v.place(), Carrier.AT_END);
            case TokenDoc.At a -> slots(a.doc(), into);
            case TokenDoc.Node n -> slots(n.doc(), into);
            case TokenDoc.Nest n -> slots(n.doc(), into);
            case TokenDoc.Group g -> slots(g.doc(), into);
            case TokenDoc.Concat c -> c.parts().forEach(part -> slots(part, into));
            case TokenDoc.Nil _, TokenDoc.Token _, TokenDoc.Comment _, TokenDoc.Trailing _,
                    TokenDoc.Gap _, TokenDoc.MustBreak _ -> { }
        }
    }

    /** {@code doc} with every carrier slot filled, and none of them left. */
    static TokenDoc resolve(TokenDoc doc, Held held) {
        return rewrite(doc, held);
    }

    private static TokenDoc rewrite(TokenDoc doc, Held held) {
        return switch (doc) {
            // The place is where the carrier stood, before whatever it carries: a comment
            // written there is at the place and not the other way round.
            case TokenDoc.Carries c -> TokenDoc.concat(TokenDoc.pointOf(c.place()),
                    written(c, held));
            case TokenDoc.PointOf p -> p;
            case TokenDoc.Vacant v -> filled(v, held);
            case TokenDoc.At a -> new TokenDoc.At(a.place(), rewrite(a.doc(), held));
            case TokenDoc.Node n -> new TokenDoc.Node(n.kind(), rewrite(n.doc(), held));
            case TokenDoc.Nest n -> new TokenDoc.Nest(n.indent(), rewrite(n.doc(), held));
            case TokenDoc.Group g -> new TokenDoc.Group(rewrite(g.doc(), held));
            case TokenDoc.Concat c -> {
                List<TokenDoc> parts = new ArrayList<>();
                for (TokenDoc part : c.parts()) {
                    parts.add(rewrite(part, held));
                }
                yield new TokenDoc.Concat(List.copyOf(parts));
            }
            case TokenDoc.Nil _, TokenDoc.Token _, TokenDoc.Comment _, TokenDoc.Trailing _,
                    TokenDoc.Gap _, TokenDoc.MustBreak _ -> doc;
        };
    }

    /**
     * What brackets with no member between them are written as.
     *
     * <p>Nothing between them holds one boundary and not two: written as two — one just inside each
     * bracket — what a construct written open put there was two spaces, and no rule had said so.
     * With a comment between them the comments stand where a member would have, so they bring no
     * line of their own; the brackets already open and close one, and the
     * {@link TokenDoc#MUST_BREAK} is what stops the layout from putting that line back together.
     */
    private static TokenDoc filled(TokenDoc.Vacant vacant, Held held) {
        List<TokenDoc> comments = held.at(vacant.place(), Carrier.AT_END);
        if (comments.isEmpty()) {
            return TokenDoc.node(vacant.construct(),
                    TokenDoc.concat(vacant.open(), TokenDoc.GAP, vacant.close()));
        }
        return TokenDoc.node(vacant.construct(), TokenDoc.group(TokenDoc.concat(
                vacant.open(),
                TokenDoc.nest(vacant.indent(), TokenDoc.concat(TokenDoc.SOFT_GAP,
                        TokenDoc.MUST_BREAK, TokenDoc.join(
                                TokenDoc.forced(Obligation.NOTHING_SHARES_A_COMMENTS_LINE),
                                comments))),
                TokenDoc.SOFT_GAP, vacant.close())));
    }

    /**
     * What a filled slot is written as.
     *
     * <p>A comment written above the place goes on a line of its own, and the forced boundary
     * after it is what makes the enclosing group break: a {@code //} on a line the group had
     * collapsed would swallow everything after it.
     */
    private static TokenDoc written(TokenDoc.Carries slot, Held held) {
        List<TokenDoc> comments = held.at(slot.place(), slot.which());
        if (comments.isEmpty()) {
            return TokenDoc.NIL;
        }
        List<TokenDoc> parts = new ArrayList<>();
        for (TokenDoc c : comments) {
            switch (slot.which()) {
                case ABOVE -> parts.add(TokenDoc.concat(c,
                        TokenDoc.forced(Obligation.NOTHING_SHARES_A_COMMENTS_LINE)));
                case TRAILING -> parts.add(c);
                case BELOW, AT_END -> parts.add(TokenDoc.concat(
                        TokenDoc.forced(Obligation.NOTHING_SHARES_A_COMMENTS_LINE), c));
            }
        }
        return TokenDoc.concat(parts);
    }
}
