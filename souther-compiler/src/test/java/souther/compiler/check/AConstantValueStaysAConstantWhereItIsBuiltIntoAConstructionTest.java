package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;

import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value the compile-time fold evaluates is a constant wherever it is named, however it is written.
 *
 * <p>What every reader of a constant folds is a tree, and a call to a method is a name it cannot
 * fold. A value that folds because it applies a library operation to a literal is therefore kept
 * out of the values emitted as methods, so a construction of it is one the compile-time check of a
 * construction still reads.
 */
class AConstantValueStaysAConstantWhereItIsBuiltIntoAConstructionTest {

    private static final String MODULE = """
            module m exposing (go, Pos)

            let zero = String.length("a")

            data Pos = Int
                invariant value >= 1

            behavior go : (n: Int) -> Pos
                constructs Pos
            let go (n) = Pos(zero)
            """;

    private static int callsOfValues(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] held = {e instanceof Hir.ValueInvocation ? 1 : 0};
        Hir.forEachChild(e, child -> held[0] += callsOfValues(child));
        return held[0];
    }

    private static final String SHARED = """
            module m exposing (f)

            let a = String.length("abc")
            let x = List.length([a])
            let y = List.length([a, a])
            let z = x + y

            behavior f : (n: Int) -> Int
            let f (n) = z
            """;

    private static int builds(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] held = {e instanceof Hir.Materialised || e instanceof Hir.ValueInvocation ? 1 : 0};
        Hir.forEachChild(e, child -> held[0] += builds(child));
        return held[0];
    }

    @Test
    void aConstantTwoMethodValuesNameIsBuiltOnceByTheRegionThatBuildsThem() {
        Hir.Expr body = Compiler.compiled(SHARED, "m").db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName("f")))
                .value().value().definition().writtenBody();

        assertEquals(4, builds(body),
                "a, x, y and z each built once here: a method that built the constant itself would"
                        + " leave x and y called and a built by each of them");
    }

    @Test
    void aConstructionOfAFoldedValueThatViolatesTheRuleIsRefused() {
        CompileException refused = assertThrows(CompileException.class,
                () -> Compiler.compile(MODULE.replace("\"a\"", "\"\"")));
        assertTrue(refused.getMessage().contains("E2010"), refused.getMessage());
    }

    @Test
    void aValueTheFoldEvaluatesIsNotCalledAsAMethod() {
        Hir.Expr body = Compiler.compiled(MODULE, "m").db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName("go")))
                .value().value().definition().writtenBody();

        assertEquals(0, callsOfValues(body),
                "the value folds to a literal, so it stands where it is named");
    }
}
