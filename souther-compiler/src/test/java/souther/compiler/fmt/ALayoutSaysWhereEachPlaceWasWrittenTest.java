package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A place is somewhere the canonical form writes something, and the layout is where it wrote it. The
 * document knows the places (#506) and the run knows the columns; between them the span a place
 * occupies in the text is a fact neither has been asked for.
 *
 * <p>Without it a reader of a difference has to find a place in the output by matching text, which
 * is the search the places were made to replace.
 */
class ALayoutSaysWhereEachPlaceWasWrittenTest {

    private static Formatter.CanonicalForm canonical(String source) {
        return Formatter.canonicalize(CstParser.parse(source).root());
    }

    private static Layout layoutOf(String source) {
        return canonical(source).layout();
    }

    /**
     * Every place this run's document writes is a place its layout wrote somewhere — those places,
     * by identity, and not as many of them as the document has.
     *
     * <p>The places the document writes, and not every place the run made: some of those are
     * written nowhere, which {@link #butNotEveryPlaceTheRunMakes} says and #555 settles.
     *
     * <p>This used to build the document a second time to walk it, and a second canonicalization
     * makes its own places: the two collections came out the same size and shared not one member,
     * so the count held and said nothing about the layout's places.
     */
    @Test
    void everyPlaceTheDocumentWritesHasASpan() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            Formatter.CanonicalForm canonical = canonical(source);
            List<Place> written = new ArrayList<>();
            placesOf(canonical.construction().doc(), written);
            assertEquals(List.of(), written.stream()
                            .filter(p -> !canonical.layout().spans().containsKey(p)).toList(),
                    "places this run's document writes that its layout wrote nowhere, in:\n"
                            + source);
            assertEquals(written.size(), canonical.layout().spans().size(),
                    "and no others, in:\n" + source);
        }
    }

    /**
     * A place is written inside the place that holds it. {@code Place.parent} says "the place this
     * one is written inside", and a function type used to name the bracketed run alone while its
     * result was written after it — a parent that did not hold its child.
     */
    @Test
    void andAPlaceIsWrittenInsideTheOneThatHoldsIt() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            Layout layout = layoutOf(source);
            for (Place place : layout.spans().keySet()) {
                Span span = layout.spans().get(place);
                Span above = place.parent() == null ? null : layout.spans().get(place.parent());
                if (above == null) {
                    continue;
                }
                assertTrue(above.start() <= span.start() && span.end() <= above.end(),
                        place.construct() + " at " + span + " is not inside its parent "
                                + place.parent().construct() + " at " + above + ", in:\n" + source);
            }
        }
    }

    /** And what a span covers is what was written there. */
    @Test
    void andASpanCoversWhatWasWrittenThere() {
        Layout layout = layoutOf("""
                module m
                let g (x: Int): Int = x
                """);
        List<String> covered = layout.spans().entrySet().stream()
                .filter(e -> e.getKey().construct() == souther.compiler.cst.SyntaxKind.FN_PARAM_LIST)
                .map(e -> layout.text().substring(e.getValue().start(), e.getValue().end()))
                .toList();
        assertEquals(List.of("(x: Int)"), covered);
    }

    private static void placesOf(TokenDoc doc, List<Place> out) {
        switch (doc) {
            case TokenDoc.At a -> {
                out.add(a.place());
                placesOf(a.doc(), out);
            }
            case TokenDoc.Node n -> placesOf(n.doc(), out);
            case TokenDoc.Nest n -> placesOf(n.doc(), out);
            case TokenDoc.Group g -> placesOf(g.doc(), out);
            case TokenDoc.Concat c -> c.parts().forEach(part -> placesOf(part, out));
            default -> { }
        }
    }

    /**
     * What two canonicalizations of one source share of the places and the groups they make.
     * Neither: each run makes its own, and a layout asked about the other run's answers that it
     * wrote it nowhere rather than refusing the question. Written down so that the reason a
     * canonical form is one object is a stated fact and not a habit.
     */
    @Test
    void andTwoRunsShareNoPlacesOrGroups() {
        String source = "module m\n\nlet g (x: Int): Int = x\n";
        Formatter.CanonicalForm one = canonical(source);
        Formatter.CanonicalForm other = canonical(source);

        assertEquals(one.text(), other.text());

        List<Place> theirPlaces = new ArrayList<>();
        placesOf(other.construction().doc(), theirPlaces);
        assertFalse(theirPlaces.isEmpty());
        assertEquals(List.of(),
                theirPlaces.stream().filter(p -> one.layout().spans().containsKey(p)).toList(),
                "a place of one run is not a place the other laid out");

        List<Doc.GroupRef> theirGroups = other.layout().decisions().stream()
                .map(GroupDecision::group).toList();
        List<Doc.GroupRef> ours = one.layout().decisions().stream()
                .map(GroupDecision::group).toList();
        assertFalse(theirGroups.isEmpty());
        assertEquals(theirGroups.size(), ours.size());
        assertEquals(List.of(), theirGroups.stream().filter(ours::contains).toList(),
                "and a group of one run is not a group the other decided about");
    }

    /**
     * And the places a run makes that its document writes nowhere. A place is made for the line a
     * construct opens with — a {@code data} declaration's {@code =}, a block's brace, a match's
     * {@code with} — and it carries the comment written at the end of that line while holding none
     * of the text; a construct that writes through its members, like a product body, makes a place
     * that is the parent of theirs and wraps nothing itself; and the file's own place wraps nothing
     * at all.
     *
     * <p>So the spans answer where an annotation was written, not where a place is. Stated here
     * rather than left to be found, because a witness naming one of these as a comment's owner
     * cannot say where in the output it is. What a place's location is when it writes no text of
     * its own is #555.
     */
    @Test
    void butNotEveryPlaceTheRunMakes() {
        Formatter.CanonicalForm canonical = canonical(SOURCE_WITH_A_HEADER_COMMENT);
        List<String> unlocated = canonical.places().stream()
                .filter(p -> !canonical.layout().spans().containsKey(p))
                .map(p -> p.construct() + (p.parent() == null ? " (the file)" : ""))
                .toList();

        assertEquals(List.of("SOURCE_FILE (the file)", "ASSIGN", "PRODUCT_BODY"), unlocated,
                "the file, the anchor that carries the header line's comment, and the parent of the"
                        + " fields \u2014 none of them locatable in the output");
    }

    private static final String SOURCE_WITH_A_HEADER_COMMENT =
            "module m\ndata D =   // about the block\n    { a: Int\n    , b: Int\n    }\n";
}
