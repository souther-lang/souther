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
     * Every place a canonicalization made is a place its layout wrote somewhere — those places, by
     * identity, and not as many places as it made.
     *
     * <p>This used to build the document a second time to walk it, and a second canonicalization
     * makes its own places: the two collections came out the same size and shared not one member,
     * so the count held and said nothing about the layout's places.
     */
    @Test
    void everyPlaceOfTheRunHasASpan() {
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
     * What two canonicalizations of one source share. Nothing: each makes its own places, and a
     * layout asked about another run's place answers that it wrote it nowhere rather than refusing
     * the question. Written down so that the reason a canonical form is one object is a stated fact
     * and not a habit.
     */
    @Test
    void andTwoRunsShareNoneOfIt() {
        String source = "module m\n\nlet g (x: Int): Int = x\n";
        Formatter.CanonicalForm one = canonical(source);
        Formatter.CanonicalForm other = canonical(source);

        assertEquals(one.text(), other.text());
        List<Place> theirs = new ArrayList<>();
        placesOf(other.construction().doc(), theirs);
        assertFalse(theirs.isEmpty());
        assertEquals(List.of(),
                theirs.stream().filter(p -> one.layout().spans().containsKey(p)).toList(),
                "a place of one run is not a place the other laid out");
    }
}
