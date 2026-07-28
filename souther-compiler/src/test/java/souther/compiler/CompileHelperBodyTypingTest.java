package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A helper's parameter takes its type from the helper's own body, never from its callers (spec 13.1,
 * issue #176). The body determines it where it reaches a position that names a type — an operator
 * against a value of known type, an argument of a call whose parameter is declared, a field of a
 * construction, an {@code if} condition. Where it does not, the parameter is annotated; the report
 * names the use that left it open.
 */
class CompileHelperBodyTypingTest {

    /** Compiles a module whose only helper is {@code helper}, uncalled — so only its body can type it. */
    private static boolean bodyTypes(String helper) {
        String src = """
                module demo
                data X = Int
                behavior f : (x: X) -> X
                %s
                let f (x) = x
                """.formatted(helper);
        return Compiler.compile(src).containsKey("demo.F");
    }

    /** Applies {@code demo.F} to {@code in} decoded as {@code dataType}, and encodes the result back. */
    private long applyToInt(String src, String dataType, long in) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object behavior = loader.loadClass("demo.F$Impl").getConstructor().newInstance();
        Object out = Codecs.apply(behavior, Codecs.decoded(loader, dataType, in));
        return (long) Codecs.encode(loader, dataType, out);
    }

    @Test
    void arithmeticInTheBodyTypesTheParameterWithNoCallSiteAtAll() {
        // `x * 2` fixes `x` to Int on its own. Nothing calls `double`, and nothing needs to.
        assertTrue(bodyTypes("let double (x) = x * 2"),
                "the body types `x`, so an uncalled helper compiles");
    }

    @Test
    void anIfConditionTypesTheParameter() {
        assertTrue(bodyTypes("let pick (b) = if b then 1 else 0"), "the `if` condition types `b` as Bool");
    }

    @Test
    void aLogicalOperatorTypesTheParameter() {
        assertTrue(bodyTypes("let both (b) = b && true"), "`&&` types `b` as Bool");
    }

    @Test
    void anIntrinsicsDeclaredParameterTypesIt() {
        // `String.trim` is a shipped primitive rather than a self-hosted helper, so it is not inlined
        // away; its declared parameter is what types `s`.
        assertTrue(bodyTypes("let clean (s) = String.trim(s)"), "`String.trim` types `s` as String");
    }

    @Test
    void anAnnotatedCalleeTypesTheArgumentEvenWhereItsOwnBodyDoesNot() {
        // `s` is passed where `describe` declares `note: String`. That declared type is what types
        // `s` — the callee's body never puts `note` in a position that names a type.
        assertTrue(bodyTypes("""
                let describe (n: Int, note: String) = if n > 0 then note else "none"
                let go (s) = describe(1, s)"""),
                "the callee's declared parameter types the argument");
    }

    @Test
    void aBindingOfTheSameNameShadowsTheParameter() {
        // The inner `n` is a String; it is a different `n`, so it says nothing about the parameter.
        // The parameter is typed by `n * 2`, which is the `n` the helper declares.
        assertTrue(bodyTypes("""
                let g (n) = {
                    let y = {
                        let n = "  s  "
                        String.length(String.trim(n))
                    }
                    n * 2 + y
                }"""),
                "a shadowing binding does not type the parameter");
    }

    @Test
    void aShadowingLambdaApplicationDoesNotMakeTheParameterAFunction() {
        // The applied `h` is the inner lambda binding, not the parameter, so the parameter is not
        // read as function-typed; `h * 2` types it as Int.
        assertTrue(bodyTypes("""
                let g (h) = {
                    let y = {
                        let h = (s) -> String.length(String.trim(s))
                        h("ab")
                    }
                    h * 2 + y
                }"""),
                "an application of a shadowing binding is not an application of the parameter");
    }

    @Test
    void aBodyTypedParameterStillInlinesAtItsCallSite() throws Exception {
        String src = """
                module demo
                data X = Int
                behavior f : (x: X) -> X constructs X
                let double (x) = x * 2
                let f (x) = X(double(x.value))
                """;
        assertEquals(6L, applyToInt(src, "demo.X", 3L));
    }

    @Test
    void anAnnotatedHelperItCallsTypesTheParameter() throws Exception {
        // `x` is passed to `twice`, whose parameter is declared Int, so `x` is Int.
        String src = """
                module demo
                data X = Int
                behavior f : (x: X) -> X constructs X
                let twice (n: Int) = n * 2
                let quad (x) = twice(twice(x))
                let f (x) = X(quad(x.value))
                """;
        assertEquals(12L, applyToInt(src, "demo.X", 3L));
    }

    @Test
    void aRecursiveHelpersDeclaredParameterTypesIt() throws Exception {
        // A recursive helper writes its parameter types, so a call to one types the argument passed.
        String src = """
                module demo
                data N = Int
                behavior f : (n: N) -> N constructs N
                partial let depth (n: Int): Int = if n == 0 then 0 else depth(n - 1) + 1
                let start (m) = depth(m)
                let f (n) = N(start(n.value))
                """;
        assertEquals(3L, applyToInt(src, "demo.N", 3L));
    }

    @Test
    void aNewtypeConstructorTypesTheParameter() throws Exception {
        // `Money(v)` is a construction of the newtype's `value` field, so `v` takes the type it wraps.
        String src = """
                module demo
                data Money = Int
                behavior f : (m: Money) -> Money constructs Money
                let wrap (v) = Money(v)
                let f (m) = wrap(m.value * 2)
                """;
        assertEquals(6L, applyToInt(src, "demo.Money", 3L));
    }

    @Test
    void aConstructionFieldTypesTheParameter() throws Exception {
        // `n` is the value of `amount`, whose field type is Int.
        String src = """
                module demo
                data Money = { amount: Int }
                behavior f : (m: Money) -> Money constructs Money
                let wrap (n) = Money { amount = n }
                let f (m) = wrap(m.amount * 2)
                """;
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(src), getClass().getClassLoader());
        Object m = Codecs.decoded(loader, "demo.Money", java.util.Map.of("amount", 4L));

        Object behavior = loader.loadClass("demo.F$Impl").getConstructor().newInstance();

        java.util.Map<?, ?> out = (java.util.Map<?, ?>) Codecs.encode(
                loader, "demo.Money", Codecs.apply(behavior, m));
        assertEquals(8L, out.get("amount"));
    }

    @Test
    void anInjectedBehaviorsSignatureTypesTheParameter() {
        // The helper calls an injected behavior, whose declared input types the argument it is given.
        String src = """
                module demo
                data CustomerId = String
                data Customer = { name: String }
                data Out = { name: String }
                behavior findCustomer : (id: CustomerId) -> Customer
                behavior show : (id: CustomerId) -> Out requires findCustomer constructs Out
                let nameOf (id) = findCustomer(id).name
                let show (id, findCustomer) = Out { name = nameOf(id) }
                """;
        assertTrue(Compiler.compile(src).containsKey("demo.Show"),
                "`findCustomer`'s declared input types `id` as CustomerId");
    }

    @Test
    void aCallSiteNoLongerTypesAParameter() {
        // `id`'s body says nothing about `v`. That the only call passes an Int is not consulted:
        // a helper is typed by its body, not by its callers.
        String src = """
                module demo
                data X = Int
                behavior f : (x: X) -> X constructs X
                let id (v) = v
                let f (x) = X(id(x.value))
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("check.helper.infer", e.diagnostic().messageKey(), e.getMessage());
        assertTrue(e.getMessage().contains("id") && e.getMessage().contains("v"), e.getMessage());
    }

    @Test
    void aFieldAccessDoesNotTypeTheParameterAndTheReportNamesTheUse() {
        // `line.qty` reads a field off `line` without naming a type — no type is determined by it
        // (F# reports the same shape). The report points at the use that left the parameter open.
        String src = """
                module demo
                data Line = { qty: Int, price: Int }
                data X = Int
                behavior f : (l: Line) -> X constructs X
                let total (line) = line.qty * line.price
                let f (l) = X(total(l))
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("check.helper.infer", e.diagnostic().messageKey(), e.getMessage());
        assertFalse(e.diagnostic().secondary().isEmpty(), "the open use is labelled");
        assertEquals("check.helper.infer.use", e.diagnostic().secondary().get(0).labelKey());
        assertEquals(5, e.diagnostic().secondary().get(0).region().start().line(),
                "the label sits on `line.qty`, the use that names no type");
    }

    @Test
    void aFunctionParameterIsStillAnnotated() {
        // `g` is applied in the body, so it is a function; a function type is not determined by the
        // application, and the inliner needs the annotation to expand the call.
        String src = """
                module demo
                data X = Int
                behavior f : (x: X) -> X constructs X
                let apply (g, v: Int) = g(v)
                let f (x) = X(apply((n) -> n * 2, x.value))
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("check.helper.fnparam", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void aRecursiveHelperStillAnnotatesItsParameters() {
        // A recursive helper is lowered to a method and typed on its declaration, so it writes its
        // parameter types even where a body use would determine them.
        String src = """
                module demo
                data N = Int
                behavior f : (n: N) -> N constructs N
                let count (n): Int = if n == 0 then 0 else count(n - 1) + 1
                let f (n) = N(count(n.value))
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("check.helper.annotate", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void aLyingReturnTypeIsRejectedOnABodyTypedParameter() {
        // The declared return type is checked against the body on the completed environment, whether
        // the parameter was written or determined by the body.
        String src = """
                module demo
                data X = Int
                behavior f : (x: X) -> X constructs X
                let g (n): String = n * 2
                let f (x) = x
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("check.helper.return", e.diagnostic().messageKey(), e.getMessage());
    }

    @Test
    void anAnnotatedHelperIsUnchanged() {
        String src = """
                module demo
                data X = Int
                behavior f : (x: X) -> X constructs X
                let positive (v: Int) = v >= 0
                let f (x) = if positive(x.value) then x else X(0)
                """;
        assertTrue(Compiler.compile(src).containsKey("demo.F"), "the annotated-helper form still compiles");
    }
}
