package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A spread of a value is a reference of it, and reads what every other reference in the region
 * reads.
 *
 * <p>A spread names a value the way any other position does (ADR-0072). Answered by a path of its
 * own it would be a second materialisation: one construction spreading a value and reading a field
 * off it by name would build that value twice, and so would two spreads of it.
 *
 * <p>Counted over the tree the backend emits from, as the constructions standing in it. The body
 * writes one of its own and the value writes one; a spread answered apart writes the value's again.
 */
class ASpreadReadsTheMaterialisationItsNameReadsTest {

    private static final String SOURCE = """
            module m exposing (f, Point)

            data Point =
                { x: Int
                , y: Int
                }

            let origin = Point { x = 0, y = 0 }

            behavior f : (n: Int) -> Point
            let f (n) = Point { ...origin, x = origin.y }
            """;

    /** Both constructions: the one the body writes, and the one the value writes, once. */
    private static final int BUILT = 2;

    @Test
    void aValueSpreadAndNamedInOneRegionIsBuiltOnce() {
        Compilation compiled = Compiler.compiled(SOURCE, "m");
        assertEquals("{0=[]}", String.valueOf(compiled.diagnostics()),
                "the source this counts over was refused");
        Hir.Expr body = compiled.db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName("f")))
                .value().value().writtenBody();
        assertEquals(BUILT, constructions(body),
                "a value spread in one place and named in another was built once per place, so a"
                        + " spread is answered apart from every other reference of the name");
    }

    private static int constructions(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] held = {e instanceof Hir.NewData ? 1 : 0};
        Hir.forEachChild(e, child -> held[0] += constructions(child));
        return held[0];
    }
}
