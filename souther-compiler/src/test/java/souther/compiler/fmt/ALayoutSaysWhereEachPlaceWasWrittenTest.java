package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A place is somewhere the canonical form writes something, and the layout is where it wrote it. The
 * document knows the places (#506) and the run knows the columns; between them the span a place
 * occupies in the text is a fact neither has been asked for.
 *
 * <p>Without it a reader of a difference has to find a place in the output by matching text, which
 * is the search the places were made to replace.
 */
class ALayoutSaysWhereEachPlaceWasWrittenTest {

    private static Layout layoutOf(String source) {
        return Formatter.document(CstParser.parse(source).root()).resolve().layout(100);
    }

    /** Every place the document holds is a place the layout wrote somewhere. */
    @Test
    void everyPlaceOfTheDocumentHasASpan() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            Layout layout = layoutOf(source);
            List<Place> written = new ArrayList<>();
            placesOf(Formatter.document(CstParser.parse(source).root()), written);
            assertEquals(written.size(), layout.spans().size(),
                    "one span per place, in:\n" + source);
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
}
