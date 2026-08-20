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

    /** `setState` builds a `CookLine` around a case two calls in, and neither is declared. */
    private static final String TWO_NAMES_SHORT = """
            module repro exposing ( Ticket, CookLine, ItemCookState, Pending, InProgress, Done, start )

            data Pending = { at: Int }
            data InProgress = { since: Int }
            data Done = { at: Int }
            data ItemCookState = Pending | InProgress | Done
            data CookLine = { state: ItemCookState }
            data Ticket = { lines: List<CookLine> }

            let setState (next: ItemCookState, lines: List<CookLine>): List<CookLine> =
                List.map(l -> CookLine { state = next }, lines)

            behavior start : (t: Ticket) -> Ticket
                constructs Ticket

            let start (t) = Ticket { lines = setState(InProgress { since = 0 }, t.lines) }
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
        // `wrap` is reached before the `Out` around it is built, and the cases handed to it are
        // written before the record that holds them.
        List<String> said = bodiesOf(failure("""
                module repro exposing ( Out, Wrap, Flag, Hi, Lo, f )

                data Hi = { n: Int }
                data Lo = { n: Int }
                data Flag = Hi | Lo
                data Wrap = { flag: Flag }
                data Out = { wraps: List<Wrap> }

                let wrap (flags: List<Flag>): List<Wrap> = List.map(x -> Wrap { flag = x }, flags)

                behavior f : (o: Out) -> Out
                    constructs Out

                let f (o) = Out { wraps = wrap([ Hi { n = 1 }, Lo { n = 0 } ]) }
                """));

        assertEquals(3, said.size(), said.toString());
        assertTrue(said.get(0).contains("`Hi`"), said.toString());
        assertTrue(said.get(1).contains("`Lo`"), said.toString());
        assertTrue(said.get(2).contains("`Wrap`"), said.toString());
    }

    @Test
    void oneNameShortIsStillOneDiagnostic() {
        CompileException e = failure("""
                module repro exposing ( Out, Flag, Hi, Lo, f )

                data Hi = { n: Int }
                data Lo = { n: Int }
                data Flag = Hi | Lo
                data Out = { flag: Flag }

                behavior f : (o: Out) -> Out
                    constructs Out

                let f (o) = Out { flag = Hi { n = 1 } }
                """);

        assertEquals(1, e.diagnostics().size(), bodiesOf(e).toString());
        assertEquals("E1002", e.code());
        assertTrue(e.getMessage().contains("`Hi`"), e.getMessage());
    }

    @Test
    void everyNameTheClauseCarriesAndNeverBuildsIsReported() {
        List<String> said = bodiesOf(failure("""
                module repro exposing ( In, Out, Refused, Held, f )

                data In = { n: Int }
                data Out = { n: Int }
                data Refused = { why: String }
                data Held = { until: Int }

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
        // Short of `Hi`, and carrying `Lo`, which the body never builds. One clause to rewrite, so
        // learning the second of them should not cost a build.
        CompileException e = failure("""
                module repro exposing ( Out, Flag, Hi, Lo, f )

                data Hi = { n: Int }
                data Lo = { n: Int }
                data Flag = Hi | Lo
                data Out = { flag: Flag }

                behavior f : (o: Out) -> Out
                    constructs Out, Lo

                let f (o) = Out { flag = Hi { n = 1 } }
                """);

        List<String> said = bodiesOf(e);
        assertEquals(2, said.size(), said.toString());
        assertTrue(said.get(0).contains("`Hi`") && said.get(0).contains("does not declare"),
                "what it is short of comes first: " + said);
        assertTrue(said.get(1).contains("`Lo`") && said.get(1).contains("never builds"),
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
                    constructs Ticket, CookLine

                let start (t) = Ticket { lines = setState(InProgress, t.lines) }
                """);
    }
}
