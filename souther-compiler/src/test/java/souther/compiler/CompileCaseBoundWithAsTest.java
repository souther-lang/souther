package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;

import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A match case's value is bound with {@code as}. A bare identifier beside the case name is the
 * positional binding of {@code Option}'s payload and is written only there — a user case is a named
 * data with no payload layer, and a primitive case's value is the whole matched value. F# draws the
 * same line: {@code | Some x} binds a payload, while a type test binds with {@code as}
 * ({@code | :? int as n}, where {@code | :? int n} does not parse).
 */
class CompileCaseBoundWithAsTest {

    private static final String DIVIDE = """
            module p exposing ( run, In, Out )
            data In = { a: Int, b: Int }
            data Out = { r: Int }
            behavior run : (i: In) -> Out constructs Out
            let run (i) = {
                let q = match Int.divide(i.a, i.b) with
                    | DivisionByZero -> 0
                    | Int %s -> n
                Out { r = q }
            }
            """;

    private static final String SUM = """
            module p exposing ( run, In, Out, Draft, Sent )
            data Draft = { id: Int }
            data Sent = { id: Int }
            data Application = Draft | Sent
            data In = { a: Int }
            data Out = { r: Int }
            behavior run : (i: In) -> Out constructs Out, Draft, Sent
            let run (i) = {
                let app = if i.a > 0 then Draft { id = i.a } else Sent { id = i.a }
                let n = match app with
                    | Draft %1$s -> %2$s.id
                    | Sent as s -> s.id
                Out { r = n }
            }
            """;

    /** The arm of a primitive-headed union binds with `as`, the form the spec shows. */
    @Test
    void aPrimitiveArmBindsWithAs() throws Exception {
        Compiler.compile(DIVIDE.formatted("as n"));
    }

    /** A bare identifier beside a primitive case is not a binding, and the message says so. */
    @Test
    void aPrimitiveArmRejectsABareIdentifier() {
        String rendered = render(assertThrows(CompileException.class,
                () -> Compiler.compile(DIVIDE.formatted("n"))));
        assertTrue(rendered.contains("| Int as n"), rendered);
    }

    /** A user case is bound the same way — the bare form is not a second spelling of `as`. */
    @Test
    void aUserCaseRejectsABareIdentifier() {
        String rendered = render(assertThrows(CompileException.class,
                () -> Compiler.compile(SUM.formatted("d", "d"))));
        assertTrue(rendered.contains("| Draft as d"), rendered);
    }

    @Test
    void aUserCaseBindsWithAs() throws Exception {
        Compiler.compile(SUM.formatted("as d", "d"));
    }

    /** An or-pattern binds the sum type, and it binds it with `as` too. */
    @Test
    void anOrPatternRejectsABareIdentifier() {
        String rendered = render(assertThrows(CompileException.class, () -> Compiler.compile("""
                module p exposing ( run, In, Out, Draft, Sent )
                data Draft = { id: Int }
                data Sent = { id: Int }
                data Application = Draft | Sent
                data In = { a: Int }
                data Out = { r: Int }
                behavior run : (i: In) -> Out constructs Out, Draft, Sent
                let run (i) = {
                    let app = if i.a > 0 then Draft { id = i.a } else Sent { id = i.a }
                    let n = match app with
                        | Draft | Sent x -> i.a
                    Out { r = n }
                }
                """)));
        assertTrue(rendered.contains("| Sent as x"), rendered);
    }

    /** Option keeps the positional binding; it is the one case with a payload to bind. */
    @Test
    void optionKeepsItsPositionalBinding() throws Exception {
        Compiler.compile("""
                module p exposing ( run, In, Out )
                data In = { xs: List<Int> }
                data Out = { r: Int }
                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let n = match List.get(0, i.xs) with
                        | Some v -> v
                        | None   -> 0
                    Out { r = n }
                }
                """);
    }

    private static String render(CompileException ex) {
        return new HumanRenderer(false).render(ex.diagnostic(), null, Locale.ENGLISH);
    }
}
