package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.query.Bodies;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What a value means as the analysis reads it is typed once for the value, not once for each
 * behavior that builds it.
 *
 * <p>A value takes nothing and names nothing of where it is built, so what is typed is the same
 * whichever behavior asked. A module in which many behaviors build one value would otherwise type
 * it as many times as there are behaviors. Held as the same tree, which is what one typing is: two
 * typings of one body are two trees that say the same thing.
 */
class AValueBuiltByTwoBehaviorsIsTypedOnceTest {

    private static final String MODEL = """
            module m exposing (f, g)

            let big = List.length([1, 2, 3]) > 2

            behavior f : (n: Int) -> Int
            let f (n) = if big then n else 0

            behavior g : (n: Int) -> Int
            let g (n) = if big then 1 else n
            """;

    @Test
    void bothBehaviorsReadTheOneTemplate() {
        Map<String, AnalysisBody> analysed = Compiler.compiled(MODEL, "m").db()
                .ask(new Bodies.Checked("m")).value().analysisBodies();

        AnalysisBody f = analysed.get("f");
        AnalysisBody g = analysed.get("g");

        assertEquals(1, f.templatesAfterTheirBuilders().size(), "`f` builds one value");
        assertEquals(1, g.templatesAfterTheirBuilders().size(), "and so does `g`");
        assertSame(f.templatesAfterTheirBuilders().getFirst(),
                g.templatesAfterTheirBuilders().getFirst(),
                "the value is typed once, and the two behaviors are handed that");
    }
}
