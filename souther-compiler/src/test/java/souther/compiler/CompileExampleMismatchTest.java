package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A failing {@code example} reports what came out against what was written. Both sides are rendered
 * as values in the notation a fixture is written in — the arm name alone says nothing when the
 * example fails inside one arm.
 */
class CompileExampleMismatchTest {

    private static String render(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return new HumanRenderer(false).render(e.diagnostic(), null, Locale.ENGLISH);
    }

    @Test
    void aWrongFieldValueShowsBothValues() {
        String rendered = render("""
                module demo
                data In = { n: Int }
                data Out = { n: Int }
                behavior double : (i: In) -> Out constructs Out
                let double (i) = Out { n = i.n * 2 }
                example double
                    | "twice" : (In { n = 3 }) -> Out { n = 7 }
                """);
        assertTrue(rendered.contains("Out { n = 6 }"), rendered);
        assertTrue(rendered.contains("Out { n = 7 }"), rendered);
    }

    @Test
    void aWrongArmStillShowsTheArm() {
        String rendered = render("""
                module demo
                data In = { n: Int }
                data Big = { n: Int }
                data Small
                behavior size : (i: In) -> Big | Small constructs Big, Small
                let size (i) = {
                    require i.n >= 10 else Small
                    Big { n = i.n }
                }
                example size
                    | "a small number is small" : (In { n = 3 }) -> Big { n = 3 }
                """);
        assertTrue(rendered.contains("Small"), rendered);
        assertTrue(rendered.contains("Big { n = 3 }"), rendered);
    }

    @Test
    void collectionsAndNewtypesReadAsTheyAreWritten() {
        String rendered = render("""
                module demo
                data Sku = String
                data In = { skus: List<Sku> }
                data Out = { first: Sku, counts: Map<String, Int>, tags: Set<String> }
                behavior run : (i: In) -> Out constructs Out, Sku
                let run (i) = Out {
                    first = Sku("apple"),
                    counts = List.fold((acc, s) -> Map.upsert(s.value, 1, c -> c + 1, acc),
                        Map.empty(), i.skus),
                    tags = Set.fromList([ "x" ])
                }
                example run
                    | "wrong on purpose" : (In { skus = [ Sku("apple"), Sku("apple") ] })
                        -> Out { first = Sku("pear"), counts = [ ("apple", 1) ], tags = [ "y" ] }
                """);
        // both sides go through the derived encoder, which writes a newtype bare — so the two read
        // against each other rather than in two different notations
        assertTrue(rendered.contains("first = \"apple\""), rendered);
        assertTrue(rendered.contains("first = \"pear\""), rendered);
        assertTrue(rendered.contains("(\"apple\", 2)"), rendered);
        assertTrue(rendered.contains("[ \"x\" ]"), rendered);
    }

    /** An empty collection reads as `[]` on either side, whether it is a list, a set, or a map — the
     * same form a fixture writes. */
    @Test
    void anEmptyCollectionReadsAsTheEmptyLiteral() {
        String rendered = render("""
                module demo
                data In = { ns: List<Int> }
                data Out = { counts: Map<String, Int>, tags: Set<String> }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { counts = Map.empty(), tags = Set.empty() }
                example run
                    | "wrong on purpose" : (In { ns = [] })
                        -> Out { counts = [ ("a", 1) ], tags = [ "x" ] }
                """);
        assertTrue(rendered.contains("counts = [], tags = []"), rendered);
    }

    @Test
    void aDateShowsAsTheDateItIs() {
        String rendered = render("""
                module demo
                import Date ( addDays )
                data In = { on: Date }
                data Out = { due: Date }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { due = addDays(14, i.on) }
                example run
                    | "two weeks on" : (In { on = Date("2026-07-01") }) -> Out { due = Date("2026-07-14") }
                """);
        assertTrue(rendered.contains("due = \"2026-07-15\""), rendered);
        assertTrue(rendered.contains("due = \"2026-07-14\""), rendered);
    }
}
