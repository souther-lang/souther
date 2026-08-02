package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A lambda's own parameter may hold a function — walking a {@code List<(Int) -> Bool>} hands each
 * element to the lambda — and applying it is no different from reading it. The inliner substitutes
 * a binding by its {@code BindingId}: {@code Ast.Var} and {@code Ast.Apply} make the same
 * substitution decision for the same {@code BindingId}, so a parameter applied inside the lambda
 * body reaches the binding its expansion introduced, whatever the parameter's declared shape.
 */
class CompileAppliedLambdaParamTest {

    private static final String ALL_OVER_FUNCTIONS = """
            module demo

            data Order = { n: Int }
            data Result = { ok: Bool }

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let fs: List<(Int) -> Bool> = [(x) -> x > 0, (x) -> x < 100]
                Result { ok = List.all((f) -> f(o.n), fs) }
            }
            """;

    @Test
    void aLambdaParameterHoldingAFunctionElementIsApplied() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(ALL_OVER_FUNCTIONS), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check$Impl").getDeclaredConstructor().newInstance();

        assertEquals(true, field(loader, check, Map.of("n", 5L), "ok"));
        assertEquals(false, field(loader, check, Map.of("n", -5L), "ok"));
    }

    private static final String MAP_OVER_FUNCTIONS = """
            module demo

            data Order = { n: Int }
            data Result = { ns: List<Int> }

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let fs: List<(Int) -> Int> = [(x) -> x + 1, (x) -> x * 2]
                Result { ns = List.map((g) -> g(o.n), fs) }
            }
            """;

    @Test
    void mapAppliesEachFunctionElementThroughTheLambdaParameter() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(MAP_OVER_FUNCTIONS), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check$Impl").getDeclaredConstructor().newInstance();

        assertEquals(List.of(11L, 20L), field(loader, check, Map.of("n", 10L), "ns"));
    }

    private static final String SHADOWED_LET = """
            module demo

            data Order = { n: Int }
            data Result = { ns: List<Int>, m: Int }

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let f: (Int) -> Int = (x) -> x + 100
                let fs: List<(Int) -> Int> = [(x) -> x + 1]
                Result { ns = List.map((f) -> f(o.n), fs), m = f(o.n) }
            }
            """;

    // Two bindings spell `f`; only the lambda parameter's BindingId is substituted by the
    // expansion, so its application reaches the element while the enclosing `let f` keeps its own.
    @Test
    void substitutionFollowsTheBindingNotTheSpelling() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(SHADOWED_LET), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check$Impl").getDeclaredConstructor().newInstance();

        assertEquals(List.of(11L), field(loader, check, Map.of("n", 10L), "ns"));
        assertEquals(110L, field(loader, check, Map.of("n", 10L), "m"));
    }

    private static final String SHADOWED_IMPORT = """
            module demo
            import List ( all )

            data Order = { n: Int, xs: List<Int> }
            data Result = { inner: Bool, outer: Bool }

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let ps: List<(Int) -> Bool> = [(x) -> x > 0]
                Result { inner = all((all) -> all(o.n), ps), outer = all((x) -> x > 0, o.xs) }
            }
            """;

    // The lambda parameter spells `all`, the name the module imports. Inside the lambda the
    // binding is what the name means, so the application is substituted to the element; outside,
    // the import still names the library function.
    @Test
    void aParameterShadowingAnImportedNameIsTheBindingWhereItIsInForce() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(SHADOWED_IMPORT), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check$Impl").getDeclaredConstructor().newInstance();

        assertEquals(true, field(loader, check, Map.of("n", 5L, "xs", List.of(1L, 2L)), "inner"));
        assertEquals(false, field(loader, check, Map.of("n", -5L, "xs", List.of(1L, 2L)), "inner"));
        assertEquals(false, field(loader, check, Map.of("n", 5L, "xs", List.of(1L, -2L)), "outer"));
    }

    // Substituting a callee wherever the binding is substituted does not make every parameter
    // applicable: the element here is an `Int`, and applying it is refused. The report reads the
    // binding's type rather than finding no binding at all, which the key does not distinguish —
    // what it pins is that the refusal is still there.
    @Test
    void applyingAParameterBoundToAValueIsStillRefused() {
        souther.compiler.diag.CompileException e =
                org.junit.jupiter.api.Assertions.assertThrows(
                        souther.compiler.diag.CompileException.class,
                        () -> Compiler.compile("""
                                module demo

                                data Order = { n: Int }
                                data Result = { ns: List<Int> }

                                behavior check : (o: Order) -> Result
                                    constructs Result

                                let check (o) = Result { ns = List.map((x) -> x(o.n), [1, 2]) }
                                """));
        assertEquals("check.apply.notfunction", e.diagnostic().messageKey());
    }

    private Object field(BytesClassLoader loader, Object check, Map<String, ?> order, String name)
            throws Exception {
        Object decoded = Codecs.decoded(loader, "demo.Order", order);
        Object r = Codecs.apply(check, decoded);
        return ((Map<?, ?>) Codecs.encode(loader, "demo.Result", r)).get(name);
    }
}
