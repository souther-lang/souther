package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A function value flows wherever its type may be written: what a name denotes does not depend on
 * the syntax that produced it. A lambda chosen at runtime is the same kind of value as a helper
 * named directly, and either may be handed to a combinator whose parameter is function-typed — once
 * the binding's type is known, by annotation or by an application the checker can read.
 */
class CompileFunctionValueFlowTest {

    private static final String ANNOTATED = """
            module demo

            data Order = { xs: List<Int>, spring: Bool }
            data Result = { ns: List<Int> }

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let f: (Int) -> Int = if o.spring then (x) -> x + 100 else (x) -> x + 1
                Result { ns = List.map(f, o.xs) }
            }
            """;

    @SuppressWarnings("unchecked")
    private List<Long> run(BytesClassLoader loader, Object check, List<Long> xs, boolean spring)
            throws Exception {
        Object order = Codecs.decoded(loader, "demo.Order", Map.of("xs", xs, "spring", spring));
        Object r = Codecs.apply(check, order);
        return (List<Long>) ((Map<?, ?>) Codecs.encode(loader, "demo.Result", r)).get("ns");
    }

    @Test
    void anAnnotatedFunctionValueIsPassedToACombinator() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(ANNOTATED), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check" + "$Impl").getDeclaredConstructor().newInstance();

        assertEquals(List.of(110L, 120L), run(loader, check, List.of(10L, 20L), true));
        assertEquals(List.of(11L, 21L), run(loader, check, List.of(10L, 20L), false));
    }

    private static final String BY_NAME = """
            module demo

            data Order = { xs: List<Int> }
            data Result = { ns: List<Int> }

            let bump (n: Int) = n + 1

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let f: (Int) -> Int = bump
                Result { ns = List.map(f, o.xs) }
            }
            """;

    // A helper's name in a value position is the function it names — the same value a lambda spelling
    // it out would be. What it denotes does not depend on which of the two the author wrote.
    @Test
    void aHelperNamedAsAValueIsTheFunctionItNames() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(BY_NAME), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check" + "$Impl").getDeclaredConstructor().newInstance();
        Object order = Codecs.decoded(loader, "demo.Order", Map.of("xs", List.of(10L, 20L)));
        Object r = Codecs.apply(check, order);
        assertEquals(List.of(11L, 21L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Result", r)).get("ns"));
    }

    private static final String OUT_OF_A_LIST = """
            module demo

            data Order = { xs: List<Int> }
            data Result = { ok: Bool }

            let positive (n: Int) = n > 0
            let negative (n: Int) = n < 0

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let fs: List<(Int) -> Bool> = [positive, negative]
                let picked = match List.get(1, fs) with
                    | Some f -> List.all(f, o.xs)
                    | None -> false
                Result { ok = picked }
            }
            """;

    // The function applied here was never named at the application: it came out of a list, which is
    // the position issue #198 opens. It runs, so the value in the list is the function itself.
    @Test
    void aFunctionTakenOutOfAListIsApplied() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(OUT_OF_A_LIST), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check" + "$Impl").getDeclaredConstructor().newInstance();

        assertEquals(true, ok(loader, check, List.of(-1L, -2L)));   // all negative
        assertEquals(false, ok(loader, check, List.of(-1L, 2L)));
    }

    private Object ok(BytesClassLoader loader, Object check, List<Long> xs) throws Exception {
        Object order = Codecs.decoded(loader, "demo.Order", Map.of("xs", xs));
        return ((Map<?, ?>) Codecs.encode(loader, "demo.Result", Codecs.apply(check, order))).get("ok");
    }

    // Without a written type the parameter types are read off the applications in this scope, and an
    // application inside a lambda is not one of them. That is a diagnostic, not an internal name.
    @Test
    void anUnannotatedFunctionAppliedOnlyInsideALambdaIsToldToStateItsType() {
        souther.compiler.diag.CompileException e =
                org.junit.jupiter.api.Assertions.assertThrows(
                        souther.compiler.diag.CompileException.class,
                        () -> Compiler.compile("""
                                module demo

                                data Order = { xs: List<Int>, spring: Bool }
                                data Result = { ns: List<Int> }

                                behavior check : (o: Order) -> Result
                                    constructs Result

                                let check (o) = {
                                    let f = if o.spring then (x) -> x + 100 else (x) -> x + 1
                                    Result { ns = List.map(f, o.xs) }
                                }
                                """));
        assertEquals("helper.the-functions-type-cannot-be-read", e.diagnostic().messageKey());
    }

    // Reading the applications must not swallow what is wrong inside one. A mistake in an argument is
    // reported as that mistake, not as a function whose type could not be inferred.
    @Test
    void aMistakeInsideAnApplicationIsReportedAsItself() {
        souther.compiler.diag.CompileException e =
                org.junit.jupiter.api.Assertions.assertThrows(
                        souther.compiler.diag.CompileException.class,
                        () -> Compiler.compile("""
                                module demo

                                data Item = { a: Int }
                                data R = { n: Int }

                                behavior run : (i: Item, flip: Bool) -> R
                                    constructs R

                                let run (i, flip) = {
                                    let f = if flip then (x) -> x + 1 else (x) -> x + 2
                                    R { n = f(i.noSuchField) }
                                }
                                """));
        assertEquals("check.access", e.diagnostic().messageKey());
    }

    // An application whose arguments this scope can read is still a constraint, even inside a lambda:
    // what puts an application out of reach is a binder below the inference point, not the lambda.
    @Test
    void anApplicationInsideALambdaOverOuterNamesStillTypesTheFunction() throws Exception {
        String src = """
                module demo

                data Order = { xs: List<Int>, v: Int, spring: Bool }
                data Result = { ns: List<Int> }

                behavior check : (o: Order) -> Result
                    constructs Result

                let check (o) = {
                    let f = if o.spring then (x) -> x + 100 else (x) -> x + 1
                    Result { ns = List.map((y) -> y + f(o.v), o.xs) }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check" + "$Impl").getDeclaredConstructor().newInstance();
        Object order = Codecs.decoded(loader, "demo.Order",
                Map.of("xs", List.of(1L, 2L), "v", 5L, "spring", true));
        assertEquals(List.of(106L, 107L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Result",
                        Codecs.apply(check, order))).get("ns"));
    }

    private static String shadowed(String caseBinding) {
        return """
                module demo

                data Order = { m: Int?, spring: Bool }
                data Result = { n: Int }

                behavior check : (o: Order) -> Result
                    constructs Result

                let check (o) = {
                    let f = if o.spring then (n) -> n + 1 else (n) -> n + 2
                    let y = 10
                    let r = f(match o.m with
                        | Some %s -> %s
                        | None -> 0)
                    Result { n = r + y }
                }
                """.formatted(caseBinding, caseBinding);
    }

    // What puts an application out of reach is a binding, not a spelling. The arm rebinds the name,
    // so the argument does not read the enclosing `y` — and whether the arm happens to spell its
    // binding `y` or `z` decides nothing about whether `f` can be typed.
    @Test
    void aRebindingInsideAnArgumentIsNotTheEnclosingName() throws Exception {
        assertEquals(sameShape(Compiler.compile(shadowed("z"))),
                sameShape(Compiler.compile(shadowed("y"))));
    }

    private static java.util.Set<String> sameShape(Map<String, byte[]> classes) {
        return classes.keySet();
    }
}
