package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Issue #71: a local binding may carry a type annotation, {@code let x: T = expr}. The declared type
 * is pushed into the bound expression the same way a record field's or a helper return's is, so a
 * value that only context can type — an empty-collection fold seed — can be pinned where it is bound
 * instead of forcing the fold into a typed position elsewhere.
 */
class CompileLetAnnotationTest {

    private static Diagnostic diagnosticOf(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return e.diagnostic();
    }

    @Test
    void anAnnotatedLocalBindsAndRuns() throws Exception {
        String src = """
                module demo
                data In = { v: Int }
                data Out = { v: Int }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let doubled: Int = i.v + i.v
                    Out { v = doubled }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("v", 21L));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(42L, out.get("v"));
    }

    // The motivating case: the fold sits in a local binding, where no surrounding declared type can
    // reach it. Without the annotation this is `check.fold.seed.untyped`.
    @Test
    void anAnnotationPinsAnEmptyMapSeedBoundToALocal() throws Exception {
        String src = """
                module demo
                import List ( fold )
                data In = { keys: List<String> }
                data Out = { m: Map<String, Int> }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let counted: Map<String, Int> =
                        fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty, i.keys)
                    Out { m = counted }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("keys", List.of("a", "b", "a")));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(Map.of("a", 2L, "b", 1L), out.get("m"));
    }

    // An annotated empty list is pinned too, and the binding is readable at that type afterwards.
    @Test
    void anAnnotationPinsAnEmptyListSeedBoundToALocal() throws Exception {
        String src = """
                module demo
                import List ( fold )
                data In = { words: List<String> }
                data Out = { lengths: List<Int> }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let lengths: List<Int> =
                        fold((acc, w) -> acc ++ [String.length(w)], [], i.words)
                    Out { lengths = lengths }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("words", List.of("a", "bbb")));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(List.of(1L, 3L), out.get("lengths"));
    }

    // A declared type the value does not have is a compile error, not a silently ignored comment. It
    // renders as its family does: the shared TYPE MISMATCH title and a found/expected diff.
    @Test
    void aLyingAnnotationIsACompileError() {
        Diagnostic d = diagnosticOf("""
                module demo
                data In = { v: Int }
                data Out = { v: Int }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let n: Int = "not a number"
                    Out { v = n }
                }
                """);
        assertEquals("check.type.mismatch.title", d.titleKey());
        assertEquals("check.let.annotation", d.messageKey());
        assertEquals("String", d.diff().actualType());
        assertEquals("Int", d.diff().expectedType());
    }

    // A function type is an ordinary type, so it may be written after the colon like any other. The
    // annotation is what says the lambda's parameter types, which the applications need not.
    @Test
    void aFunctionTypeMayBeWrittenOnALocalBinding() throws Exception {
        String src = """
                module demo
                data In = { v: Int }
                data Out = { v: Int }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let f: (Int) -> Int = (x) -> x + 1
                    Out { v = f(i.v) }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object run = loader.loadClass("demo.Run" + "$Impl").getDeclaredConstructor().newInstance();
        Object in = Codecs.decoded(loader, "demo.In", java.util.Map.of("v", 41L));
        assertEquals(42L, ((java.util.Map<?, ?>) Codecs.encode(loader, "demo.Out",
                Codecs.apply(run, in))).get("v"));
    }

    // The annotation is checked against the lambda, so a parameter count it does not have is an error
    // rather than a comment.
    @Test
    void anAnnotatedLambdaMustHaveTheParameterCountTheTypeStates() {
        Diagnostic d = diagnosticOf("""
                module demo
                data In = { v: Int }
                data Out = { v: Int }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let f: (Int, Int) -> Int = (x) -> x + 1
                    Out { v = f(i.v) }
                }
                """);
        assertEquals("helper.the-lambda-is-applied-with-another-number-of-arguments", d.messageKey());
    }

    // The annotated type is the binding's type for everything downstream: the value reaches a helper
    // that takes a `Map<String, Int>`, which the un-annotated `fold` over `Map.empty` would not.
    @Test
    void anAnnotatedBindingTypesTheValueItPassesOn() throws Exception {
        String src = """
                module demo
                import List ( fold )
                data In = { keys: List<String> }
                data Out = { n: Int }
                let entries (m: Map<String, Int>) = Map.size(m)
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let counted: Map<String, Int> =
                        fold((acc, k) -> Map.updateOrInsert(k, 1, n -> n + 1, acc), Map.empty, i.keys)
                    Out { n = entries(counted) }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("keys", List.of("a", "b", "a")));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(2L, out.get("n"));
    }

    // A lambda binding takes no annotation: a function type may be written only in a helper's
    // parameter, so whatever ordinary type is written here is a lie. The binding is expanded away at
    // its applications, so the rule is read on the surface body rather than after lowering.
    @Test
    void anAnnotationOnALambdaBindingIsRejected() {
        Diagnostic d = diagnosticOf("""
                module demo
                data In = { v: Int }
                data Out = { v: Int }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let f: Int = (x) -> x + 1
                    Out { v = f(i.v) }
                }
                """);
        assertEquals("check.fn.title", d.titleKey());
        assertEquals("helper.a-function-type-is-written-outside-a-helper-parameter", d.messageKey());
        assertEquals("f", d.values().get("binding"));
    }

    // The other shape a function binding takes — one an `if` chooses, which stays a first-class Fn
    // rather than being expanded away — is rejected by the same rule, with the same message.
    @Test
    void anAnnotationOnARuntimeChosenFunctionIsRejected() {
        Diagnostic d = diagnosticOf("""
                module demo
                data In = { v: Int }
                data Out = { v: Int }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let f: Int = if i.v > 0 then (x) -> x + 1 else (x) -> x - 1
                    Out { v = f(i.v) }
                }
                """);
        assertEquals("check.fn.title", d.titleKey());
        assertEquals("helper.a-function-type-is-written-outside-a-helper-parameter", d.messageKey());
    }

    // A sum annotation widens a case value to its sum, so the body's `match` sees both arms.
    @Test
    void anAnnotationMayWidenACaseValueToItsSum() throws Exception {
        String src = """
                module demo
                data In = { v: Int }
                data Big = { v: Int }
                data Small = { v: Int }
                behavior run : (i: In) -> Big | Small constructs Big, Small
                let run (i) = {
                    let sized: Big | Small = if i.v > 10 then Big { v = i.v } else Small { v = i.v }
                    match sized with
                        | Big as b   -> b
                        | Small as s -> s
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Object big = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("v", 11L)));
        assertEquals("demo.Big", big.getClass().getName());
        Object small = Codecs.apply(behavior, Codecs.decoded(loader, "demo.In", Map.of("v", 1L)));
        assertEquals("demo.Small", small.getClass().getName());
    }

    // A newtype binding: the annotation names the newtype, and the value is one.
    @Test
    void anAnnotationMayNameANewtype() throws Exception {
        String src = """
                module demo
                data 金額 = Int
                data In = { v: Int }
                data Out = { total: 金額 }
                behavior run : (i: In) -> Out constructs Out, 金額
                let run (i) = {
                    let total: 金額 = 金額(i.v + 1)
                    Out { total = total }
                }
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object in = Codecs.decoded(loader, "demo.In", Map.of("v", 9L));
        Object behavior = loader.loadClass("demo.Run" + "$Impl").getConstructor().newInstance();
        Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out", Codecs.apply(behavior, in));
        assertEquals(10L, out.get("total"));
    }
}
