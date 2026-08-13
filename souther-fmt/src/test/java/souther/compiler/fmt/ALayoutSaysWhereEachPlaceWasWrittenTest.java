package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a place's extent covers, and what two canonicalizations of one source share. The
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



    /** And what a span covers is what was written there. */
    @Test
    void andASpanCoversWhatWasWrittenThere() {
        Layout layout = layoutOf("""
                module m
                let g (x: Int): Int = x
                """);
        List<String> covered = layout.extents().entrySet().stream()
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
                theirPlaces.stream().filter(p -> one.layout().extents().containsKey(p)).toList(),
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
}
