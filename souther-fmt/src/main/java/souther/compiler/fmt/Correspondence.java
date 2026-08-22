package souther.compiler.fmt;

import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * The places of the canonical form, and what the source had at each.
 *
 * <p>A relation in both directions, and nothing here assumes otherwise. A place may stand for
 * nothing the source wrote, and one source element may stand behind several places. Nothing hands
 * back <em>the</em> source element of a place, because for a definition written as a lambda there
 * is no such thing: the parameter-list place the canonical form writes stands for the lambda, and
 * the body place beside it stands for that lambda's last expression child. A single-valued answer
 * would have to pick one of those, and picking is what asking the source tree again already does.
 *
 * <p>Places are made here so that which of its parent's places a place is, is counted once.
 */
final class Correspondence {

    private final Place file = new Place(null, SyntaxKind.SOURCE_FILE, Opening.FILE_BEGINS);
    private final Map<Place, List<Written>> wrote = new IdentityHashMap<>();
    private final Map<Written, List<Place>> at = new HashMap<>();
    private final Map<SyntaxNode, Span> spans = new IdentityHashMap<>();
    private final List<Place> made = new ArrayList<>();

    /** The file's place, which the construction declared. Asking for it does not make one. */
    Place file() {
        return file;
    }

    /** Says what the source has at the file's own place. It is made before anything is written, so
     *  it is the one place that is told rather than asked. */
    Place fileOf(SyntaxNode source) {
        made.add(file);
        wrote.put(file, List.of(new Written.Construct(source)));
        at.computeIfAbsent(new Written.Construct(source), _ -> new ArrayList<>()).add(file);
        return file;
    }

    /**
     * A place written under {@code parent}, standing as {@code opening} says, for the source
     * elements in {@code from} — none, one, or several of them.
     *
     * <p>Declaring a place is not deciding where a comment goes. That is decided over the places
     * once they all exist, which is the whole of the difference this makes.
     */
    Place under(Place parent, SyntaxKind construct, Opening opening, Written... from) {
        Place place = new Place(parent, construct, opening);
        made.add(place);
        if (from.length > 0) {
            wrote.put(place, List.of(from));
            for (Written w : from) {
                at.computeIfAbsent(w, _ -> new ArrayList<>()).add(place);
            }
        }
        return place;
    }

    /** Every place the construction made, the file's first, each once. Not all of them are written
     *  in the document — the file's is not, and neither is one naming the line a construct opens
     *  with — so where each of them is is {@link Layout}'s to say and not this order's. */
    List<Place> made() {
        return List.copyOf(made);
    }

    /** Where a construct the canonical form writes no place of its own for begins and ends: the
     *  first place its text is written at and the last. The two are the same place for a construct
     *  written inside one. */
    record Span(Place from, Place to) {}

    /** Records that {@code node}'s text is written at {@code at} and nowhere else — a type inside a
     *  field's line, a name inside an import's. */
    void within(SyntaxNode node, Place at) {
        spans.putIfAbsent(node, new Span(at, at));
    }

    /** Records that {@code node} is written as a run of places, opening at {@code from} and ending
     *  at {@code to}. This is what a flattened chain leaves: the source's nesting is written as
     *  siblings, so the construct the parser read is spread over several of them. */
    void spanning(SyntaxNode node, Place from, Place to) {
        spans.put(node, new Span(from, to));
    }

    /** Where {@code node} is written, or null where the construction recorded nothing for it. */
    Span spanOf(SyntaxNode node) {
        return spans.get(node);
    }

    /** What the source had at {@code place}. Empty where the canonical form writes something the
     *  source has nothing at. */
    List<Written> sourcesOf(Place place) {
        return wrote.getOrDefault(place, List.of());
    }

    /**
     * The places {@code written} stands behind. Empty where the canonical form does not write it,
     * and more than one where it stands behind more than one.
     *
     * <p>In no order. This is a relation, and the order the places were made is the order the
     * formatter's methods happened to run in — the implementation trace that a place's own
     * position was taken off {@link Place#orderedIn} to stop being. A caller that needs the places
     * in the order they are written asks for that order.
     */
    List<Place> placesOf(Written written) {
        return at.getOrDefault(written, List.of());
    }
}
