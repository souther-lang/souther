package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;

import org.junit.jupiter.api.Test;

import java.util.Locale;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code match} case may destructure a newtype in the pattern with the constructor form
 * {@code X(inner)}, the inverse of construction {@code X(v)}. Nesting it reaches through a
 * newtype-over-newtype in one pattern — {@code | アクティベート済み(メールアドレス(s)) -> s} binds
 * {@code s} to the base String — so {@code .value.value} accessor chains are not written.
 */
class CompileMatchNewtypeUnwrapTest {

    private static final String HEAD = """
            module demo

            data メールアドレス = String
            data アクティベート済み = メールアドレス
            data 未アクティベート = メールアドレス
            data メール = アクティベート済み | 未アクティベート

            behavior addr : (m: メール) -> String

            let addr (m) =
            """;

    private Object run(String matchBody, Map<String, Object> input) throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(HEAD + matchBody), getClass().getClassLoader());
        Object mail = Codecs.decoded(loader, "demo.メール", input);
        Object behavior = Emitted.behavior(loader, "demo", "addr").getConstructor().newInstance();
        return Codecs.apply(behavior, mail);
    }

    @Test
    void nestedDestructureBindsTheBaseValue() throws Exception {
        String body = """
                    match m with
                        | アクティベート済み(メールアドレス(s)) -> s
                        | 未アクティベート(メールアドレス(s)) -> s
                """;
        assertEquals("a@b", run(body, Map.of("type", "アクティベート済み", "value", "a@b")));
        assertEquals("c@d", run(body, Map.of("type", "未アクティベート", "value", "c@d")));
    }

    @Test
    void shortFormBindsTheIntermediateNewtype() throws Exception {
        // `アクティベート済み(a)` binds `a` to the intermediate メールアドレス; `.value` reads its String
        String body = """
                    match m with
                        | アクティベート済み(a) -> a.value
                        | 未アクティベート(a) -> a.value
                """;
        assertEquals("a@b", run(body, Map.of("type", "アクティベート済み", "value", "a@b")));
    }

    @Test
    void aWrongInnerNameIsRejected() {
        // アクティベート済み wraps メールアドレス, not ソース — the inner name must match (Elm/F# parity)
        String body = """
                    match m with
                        | アクティベート済み(ソース(s)) -> s
                        | 未アクティベート(メールアドレス(s)) -> s
                """;
        CompileException ex = assertThrows(CompileException.class, () -> Compiler.compile(HEAD + body));
        assertTrue(ex.getMessage().contains("ソース") || ex.getMessage().contains("メールアドレス"), ex.getMessage());
    }

    private static final String PRODUCT_HEAD = """
            module demo

            data 中身 = { value: String }
            data 空
            data S = 中身 | 空

            behavior f : (s: S) -> String

            let f (s) =
            """;

    @Test
    void aProductCaseIsNotOpenedWithTheConstructorForm() {
        // 中身 is a product (even though it has a field named `value`), not a newtype — `中身(v)`
        // must be rejected, not silently bound to the `value` field.
        String body = """
                    match s with
                        | 中身(v) -> v
                        | 空 -> "x"
                """;
        CompileException ex = assertThrows(CompileException.class, () -> Compiler.compile(PRODUCT_HEAD + body));
        assertTrue(ex.getMessage().contains("中身"), ex.getMessage());
    }

    @Test
    void aPrimitiveNameCannotBeOpenedAsALayer() {
        // メールアドレス wraps String; String is not a newtype, so `メールアドレス(String(s))` is rejected
        String body = """
                    match m with
                        | アクティベート済み(メールアドレス(String(s))) -> s
                        | 未アクティベート(メールアドレス(s)) -> s
                """;
        CompileException ex = assertThrows(CompileException.class, () -> Compiler.compile(HEAD + body));
        assertTrue(ex.getMessage().contains("String"), ex.getMessage());
    }

    @Test
    void aTrailingIdentifierAfterTheParenIsRejected() {
        String body = """
                    match m with
                        | アクティベート済み(メールアドレス(s)) extra -> s
                        | 未アクティベート(メールアドレス(s)) -> s
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(HEAD + body));
    }

    @Test
    void aParenDestructureOnAnOrPatternIsRejected() {
        String body = """
                    match m with
                        | アクティベート済み | 未アクティベート(a) -> a.value
                """;
        CompileException ex = assertThrows(CompileException.class, () -> Compiler.compile(HEAD + body));
        assertTrue(render(ex).contains("or-pattern"), render(ex));
    }

    /** Every one of these rejections is read as rendered prose, and each of the three used to reach
     *  the reader as its own message key. */
    @Test
    void eachRejectionRendersAsAMessage() {
        String wrongInner = """
                    match m with
                        | アクティベート済み(ソース(s)) -> s
                        | 未アクティベート(メールアドレス(s)) -> s
                """;
        String notNewtype = """
                    match m with
                        | アクティベート済み(メールアドレス(String(s))) -> s
                        | 未アクティベート(メールアドレス(s)) -> s
                """;
        String orPattern = """
                    match m with
                        | アクティベート済み | 未アクティベート(a) -> a.value
                """;
        for (String body : new String[] {wrongInner, notNewtype, orPattern}) {
            String rendered = render(assertThrows(CompileException.class,
                    () -> Compiler.compile(HEAD + body)));
            assertFalse(rendered.contains("check.match.newtype"), rendered);
        }
    }

    @Test
    void openingAPrimitiveCaseSaysHowToBindItInstead() {
        // `Int` heads a primitive union case, so it is bound with `as`, not opened with `(...)`
        CompileException ex = assertThrows(CompileException.class, () -> Compiler.compile("""
                module p exposing ( run, In, Out )
                data In = { a: Int, b: Int }
                data Out = { r: Int }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let q = match Int.divide(i.a, i.b) with
                        | DivisionByZero -> 0
                        | Int(n) -> n
                    Out { r = q }
                }
                """));
        String rendered = render(ex);
        assertTrue(rendered.contains("`Int` is not a newtype"), rendered);
        assertTrue(rendered.contains("| Int as v"), rendered);
    }

    private static String render(CompileException ex) {
        return new HumanRenderer(false).render(ex.diagnostic(), null, Locale.ENGLISH);
    }
}
