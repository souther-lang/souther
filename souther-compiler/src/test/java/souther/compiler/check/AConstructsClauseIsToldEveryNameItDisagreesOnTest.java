package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticRenderer;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code constructs} clause is told every name it and the body disagree on, at once.
 *
 * <p>Both sides are worked out whole before anything is reported, so stopping at the first
 * disagreement left the author to fix that one, compile, and be told the next — one build per name,
 * down whatever the call graph reaches. A clause short of one name and carrying another it never
 * builds is wrong in both directions, and that is still one clause to rewrite.
 *
 * <p>Each name is its own diagnostic — E1002 for one the clause is short of, E1006 for one it
 * carries and never builds — so each keeps the hint for the name it is about.
 */
class AConstructsClauseIsToldEveryNameItDisagreesOnTest {

    /** `setState` builds a `CookLine` around a unit case two calls in, and neither is declared. */
    private static final String TWO_NAMES_SHORT = """
            module repro exposing ( Ticket, CookLine, ItemCookState, Pending, InProgress, Done, start )

            data ItemCookState = Pending | InProgress | Done
            data CookLine = { state: ItemCookState }
            data Ticket = { lines: List<CookLine> }

            let setState (next: ItemCookState, lines: List<CookLine>): List<CookLine> =
                List.map(l -> CookLine { state = next }, lines)

            behavior start : (t: Ticket) -> Ticket
                constructs Ticket

            let start (t) = Ticket { lines = setState(InProgress, t.lines) }
            """;

    private static List<String> bodiesOf(CompileException e) {
        List<String> said = new ArrayList<>();
        for (Diagnostic d : e.diagnostics()) {
            said.add(DiagnosticRenderer.legacyBody(d));
        }
        return said;
    }

    private static CompileException failure(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }

    @Test
    void everyNameTheClauseIsShortOfIsReported() {
        List<String> said = bodiesOf(failure(TWO_NAMES_SHORT));

        assertEquals(2, said.size(), "one per name, and not the first of them: " + said);
        assertTrue(said.get(0).contains("`InProgress`"), said.toString());
        assertTrue(said.get(1).contains("`CookLine`"), said.toString());
    }

    @Test
    void eachOneIsItsOwnE1002WithItsOwnHint() {
        CompileException e = failure(TWO_NAMES_SHORT);

        for (Diagnostic d : e.diagnostics()) {
            assertEquals("E1002", d.code(), bodiesOf(e).toString());
        }
        assertTrue(bodiesOf(e).get(0).contains("Add `constructs InProgress`"), bodiesOf(e).toString());
        assertTrue(bodiesOf(e).get(1).contains("Add `constructs CookLine`"), bodiesOf(e).toString());
    }

    @Test
    void theyComeInTheOrderTheBodyBuildsThem() {
        // `setState` is reached before the `Ticket` around it is built, and inside it the unit case
        // is written before the record that holds it.
        List<String> said = bodiesOf(failure("""
                module repro exposing ( Out, Wrap, Flag, On, Off, f )

                data Flag = On | Off
                data Wrap = { flag: Flag }
                data Out = { wraps: List<Wrap> }

                let wrap (flags: List<Flag>): List<Wrap> = List.map(x -> Wrap { flag = x }, flags)

                behavior f : (o: Out) -> Out
                    constructs Out

                let f (o) = Out { wraps = wrap([ On, Off ]) }
                """));

        assertEquals(3, said.size(), said.toString());
        assertTrue(said.get(0).contains("`On`"), said.toString());
        assertTrue(said.get(1).contains("`Off`"), said.toString());
        assertTrue(said.get(2).contains("`Wrap`"), said.toString());
    }

    @Test
    void oneNameShortIsStillOneDiagnostic() {
        CompileException e = failure("""
                module repro exposing ( Out, Flag, On, Off, f )

                data Flag = On | Off
                data Out = { flag: Flag }

                behavior f : (o: Out) -> Out
                    constructs Out

                let f (o) = Out { flag = On }
                """);

        assertEquals(1, e.diagnostics().size(), bodiesOf(e).toString());
        assertEquals("E1002", e.code());
        assertTrue(e.getMessage().contains("`On`"), e.getMessage());
    }

    @Test
    void everyNameTheClauseCarriesAndNeverBuildsIsReported() {
        List<String> said = bodiesOf(failure("""
                module repro exposing ( In, Out, Refused, Held, f )

                data In = { n: Int }
                data Out = { n: Int }
                data Refused
                data Held

                behavior f : (i: In) -> Out
                    constructs Out, Refused, Held

                let f (i) = Out { n = i.n }
                """));

        assertEquals(2, said.size(), "one per name it never builds: " + said);
        assertTrue(said.get(0).contains("`Refused`"), said.toString());
        assertTrue(said.get(1).contains("`Held`"), said.toString());
        assertTrue(said.get(0).contains("Remove `Refused`"), said.toString());
    }

    @Test
    void aClauseWrongInBothDirectionsIsToldBothAtOnce() {
        // Short of `On`, and carrying `Off`, which the body never builds. One clause to rewrite, so
        // learning the second of them should not cost a build.
        CompileException e = failure("""
                module repro exposing ( Out, Flag, On, Off, f )

                data Flag = On | Off
                data Out = { flag: Flag }

                behavior f : (o: Out) -> Out
                    constructs Out, Off

                let f (o) = Out { flag = On }
                """);

        List<String> said = bodiesOf(e);
        assertEquals(2, said.size(), said.toString());
        assertTrue(said.get(0).contains("`On`") && said.get(0).contains("does not declare"),
                "what it is short of comes first: " + said);
        assertTrue(said.get(1).contains("`Off`") && said.get(1).contains("never builds"),
                "and what it carries follows: " + said);
        assertEquals("E1002", e.code(), "so the leading code is the under-declaration");
        assertEquals(List.of("E1002", "E1006"),
                e.diagnostics().stream().map(Diagnostic::code).toList());
    }

    @Test
    void aCompleteClauseIsStillComplete() {
        Compiler.compile("""
                module repro exposing ( Ticket, CookLine, ItemCookState, Pending, InProgress, Done, start )

                data ItemCookState = Pending | InProgress | Done
                data CookLine = { state: ItemCookState }
                data Ticket = { lines: List<CookLine> }

                let setState (next: ItemCookState, lines: List<CookLine>): List<CookLine> =
                    List.map(l -> CookLine { state = next }, lines)

                behavior start : (t: Ticket) -> Ticket
                    constructs Ticket, CookLine, InProgress

                let start (t) = Ticket { lines = setState(InProgress, t.lines) }
                """);
    }
}
