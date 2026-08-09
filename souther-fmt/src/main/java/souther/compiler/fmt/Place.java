package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

/**
 * One place of the canonical form: somewhere the formatter writes something, told apart from every
 * other place by being it.
 *
 * <p>Two siblings written as the same kind of construct are two places. An {@code if} written
 * {@code if flag then p else q} has three children that are all a {@code VAR_EXPR}, and its
 * condition, its then branch and its else branch are three places. Identity is the object's — a
 * place is not equal to another place that happens to look the same, because there is no other
 * place that is this one.
 *
 * <p>A place is not another name for a {@link souther.compiler.cst.SyntaxNode}. A definition
 * written {@code let f = (x) -> x} is written back as {@code let f (x) = x}, and the parameter list
 * there is a place the source tree has no node at. What the source had at a place is
 * {@link Correspondence}'s to say and not a field here: a place with one source element and a place
 * with none are both ordinary, and a field would make the first of those the only kind.
 *
 * <p>Which of its parent's places this is, is the label on the edge from the parent, and it is read
 * from the document by {@link #orderedIn}. Nothing else has to name it.
 */
final class Place {

    private final Place parent;
    private final SyntaxKind construct;
    private final Opening opening;

    Place(Place parent, SyntaxKind construct, Opening opening) {
        this.parent = parent;
        this.construct = construct;
        this.opening = opening;
    }

    /** The place this one is written inside, or null for the file. */
    Place parent() {
        return parent;
    }

    /** What the canonical form writes here, named as it writes it rather than as the source had
     *  it. Null where what is written is a bare name rather than a construct. */
    SyntaxKind construct() {
        return construct;
    }

    Opening opening() {
        return opening;
    }

    /**
     * Which of its parent's places each place of {@code doc} is, counted in the order the document
     * writes them.
     *
     * <p>Read from the document and not from the order the formatter made them. A declaration
     * builds its clauses before its body and writes the body first; an {@code example} builds its
     * rows before the line it opens with and writes that line first. Counting as they are made
     * records the order the formatter's methods happened to run in and calls it a fact about the
     * canonical form, which is the kind of thing a place exists to stop being asked of a trace.
     *
     * <p>Asked of the document before the carriers are answered, since a slot names the place it
     * belongs to and an answered one does not.
     */
    static Map<Place, Integer> orderedIn(TokenDoc doc) {
        List<Place> written = new ArrayList<>();
        Map<Place, Boolean> seen = new IdentityHashMap<>();
        collect(doc, written, seen);
        Map<Place, Integer> counts = new IdentityHashMap<>();
        Map<Place, Integer> out = new IdentityHashMap<>();
        for (Place p : written) {
            out.put(p, counts.merge(p.parent(), 1, Integer::sum) - 1);
        }
        return out;
    }

    private static void collect(TokenDoc doc, List<Place> written, Map<Place, Boolean> seen) {
        switch (doc) {
            case TokenDoc.At a -> {
                first(a.place(), written, seen);
                collect(a.doc(), written, seen);
            }
            case TokenDoc.Carries c -> first(c.place(), written, seen);
            case TokenDoc.Vacant v -> first(v.place(), written, seen);
            case TokenDoc.Node n -> collect(n.doc(), written, seen);
            case TokenDoc.Nest n -> collect(n.doc(), written, seen);
            case TokenDoc.Group g -> collect(g.doc(), written, seen);
            case TokenDoc.Concat c -> c.parts().forEach(part -> collect(part, written, seen));
            case TokenDoc.Nil _, TokenDoc.Token _, TokenDoc.Comment _, TokenDoc.Trailing _,
                    TokenDoc.Gap _, TokenDoc.MustBreak _ -> { }
        }
    }

    private static void first(Place place, List<Place> written, Map<Place, Boolean> seen) {
        if (place != null && seen.put(place, true) == null) {
            written.add(place);
        }
    }

    @Override
    public String toString() {
        return (parent == null ? "file" : "under " + parent.construct()) + " " + construct;
    }
}
