package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every place a canonicalization makes is somewhere in the text it came to.
 *
 * <p>Where a place is and where an annotation was written are not the same set. A construct writes
 * a region and says so; a place that names the line a construct opens with writes nothing and still
 * sits somewhere, since it carries the comment written at the end of that line; and the file's own
 * place is the whole output. Recording only the first left sixty-three places of this repository's
 * corpus with no answer, and a reader of a difference has to be able to point at any of them.
 */
class EveryPlaceIsSomewhereInTheOutputTest {

    private static Formatter.CanonicalForm canonical(String source) {
        return Formatter.canonicalize(CstParser.parse(source).root());
    }

    @Test
    void everyPlaceHasAnExtent() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            Formatter.CanonicalForm canonical = canonical(source);
            List<String> without = canonical.places().stream()
                    .filter(p -> canonical.layout().extents().get(p) == null)
                    .map(p -> String.valueOf(p.construct()))
                    .distinct()
                    .toList();
            assertEquals(List.of(), without, "places with nowhere in:\n" + source);
        }
    }

    /** A place is inside the place that holds it, by its ends and not as a set of characters: a
     * point is an empty interval, and every interval contains the empty set. */
    @Test
    void andIsInsideThePlaceThatHoldsIt() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            Formatter.CanonicalForm canonical = canonical(source);
            List<String> outside = new ArrayList<>();
            for (Place place : canonical.places()) {
                if (place.parent() == null) {
                    continue;
                }
                Extent inner = canonical.layout().extents().get(place);
                Extent outer = canonical.layout().extents().get(place.parent());
                if (!outer.contains(inner)) {
                    outside.add(place.construct() + " at " + inner + " outside "
                            + place.parent().construct() + " at " + outer);
                }
            }
            assertEquals(List.of(), outside, "in:\n" + source);
        }
    }

    /** A place that names the line a construct opens with has a position and no region. */
    @Test
    void andAnAnchorIsAPoint() {
        Formatter.CanonicalForm canonical = canonical("""
                module m

                data D =   // about the block
                    { a: Int
                    }
                """);
        List<Extent> anchors = canonical.places().stream()
                .filter(p -> p.construct() == souther.compiler.cst.SyntaxKind.ASSIGN)
                .map(p -> canonical.layout().extents().get(p))
                .toList();

        assertEquals(1, anchors.size());
        assertEquals(anchors.get(0).start(), anchors.get(0).end(), "a point, not a region");
        assertEquals("data D =", canonical.text().substring(
                canonical.text().indexOf("data D ="), anchors.get(0).start()),
                "at the insertion point, after what opens the construct and before the comment");
    }

    /** And the file's place is the output. */
    @Test
    void andTheFileIsAllOfIt() {
        Formatter.CanonicalForm canonical = canonical("module m\n\ndata D\n");
        Place file = canonical.places().stream().filter(p -> p.parent() == null)
                .findFirst().orElseThrow();
        Extent extent = canonical.layout().extents().get(file);

        assertFalse(canonical.text().isEmpty());
        assertEquals(0, extent.start());
        assertEquals(canonical.text().length(), extent.end());
    }

    /** And a comment an anchor carries can be found from where the anchor is. */
    @Test
    void andACommentAnAnchorCarriesIsFoundFromIt() {
        Formatter.CanonicalForm canonical = canonical("""
                module m

                data D =   // about the block
                    { a: Int
                    }
                """);
        Place anchor = canonical.places().stream()
                .filter(p -> p.construct() == souther.compiler.cst.SyntaxKind.ASSIGN)
                .findFirst().orElseThrow();
        Extent at = canonical.layout().extents().get(anchor);

        assertTrue(canonical.text().startsWith(" // about the block", at.start()),
                "the comment is written where the anchor is");
    }

    /**
     * And what containment means. A position is an empty interval of characters, and every interval
     * contains the empty set — read that way a point past the end of the file is inside anything.
     * The corpus cannot show it, since every place it makes is where it belongs; this can.
     */
    @Test
    void andAPointOutsideIsOutside() {
        Extent held = new Extent(10, 20);

        assertTrue(held.contains(new Extent(12, 12)), "a position between the ends is inside");
        assertTrue(held.contains(new Extent(10, 10)) && held.contains(new Extent(20, 20)),
                "and so are the ends themselves");
        assertFalse(held.contains(new Extent(30, 30)), "a position past the end is not");
        assertFalse(held.contains(new Extent(9, 9)), "nor one before the start");
    }
}
