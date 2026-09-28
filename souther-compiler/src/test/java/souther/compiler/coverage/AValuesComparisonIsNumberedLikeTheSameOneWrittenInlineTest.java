package souther.compiler.coverage;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.query.Bodies;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison a value writes is a place a run passes, however the value is emitted.
 *
 * <p>A value that needs nothing from its region is emitted as a method of its own, and a behavior
 * that names it calls it. What the numbering counts is the places of the bodies it walks, so a
 * comparison and a fork written in the value have to be among them as they are where the same
 * expression is written in the behavior.
 */
class AValuesComparisonIsNumberedLikeTheSameOneWrittenInlineTest {

    private static final String THROUGH_A_VALUE = """
            module m exposing (f)

            let big = List.length([1, 2, 3]) > 2

            behavior f : (n: Int) -> Bool
            let f (n) = if n > 0 then big else false
            """;

    private static final String WRITTEN_INLINE = """
            module m exposing (f)

            behavior f : (n: Int) -> Bool
            let f (n) = if n > 0 then List.length([1, 2, 3]) > 2 else false
            """;

    private static int placesOf(String source) {
        Bodies.Elaborated checked = Compiler.compiled(source, "m").db()
                .ask(new Bodies.Checked("m")).value();
        return checked.plan().sites().size();
    }

    @Test
    void theSamePlacesAreNumberedWhetherTheExpressionIsAValueOrIsWrittenInline() {
        int inline = placesOf(WRITTEN_INLINE);

        assertTrue(inline > 0, "the source counted over has places, or this counts nothing");
        assertEquals(inline, placesOf(THROUGH_A_VALUE),
                "a comparison the value writes is among the places a run passes");
    }
}
