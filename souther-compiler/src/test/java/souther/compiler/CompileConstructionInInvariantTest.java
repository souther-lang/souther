package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An invariant may not construct a data (spec §invariant-expressions), and it is told so however the
 * construction is spelled and however far from the clause it is written.
 *
 * <p>A newtype is constructed two ways — {@code Yen(0)} and {@code Yen { value = 0 }} — and one of
 * them is rewritten into the other before anything reads it. An invariant used to be the one place
 * that rewrite did not reach, so the call spelling survived into the check as a call to a name that
 * is not a behavior, and the author was told to implement `Yen` from Java. Both spellings are one
 * construction here.
 *
 * <p>The clause is what carries the rule, so the clause is what the diagnostic names: the
 * construction is where the error is pointed, and the clause that reaches it is labelled beside it.
 */
class CompileConstructionInInvariantTest {

    private static CompileException err(String src) {
        return assertThrows(CompileException.class, () -> Compiler.compile(src));
    }

    // --- one construction, four spellings and placements -------------------------------------

    @Test
    void theCallSpellingWrittenInTheClause() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                data Table = List<Int>
                    invariant ok = List.all(x -> Yen(0).value <= x, value)
                """);
        assertEquals("check.invariant.construct.named", e.diagnostic().messageKey());
        assertEquals(4, e.diagnostic().region().start().line());
    }

    @Test
    void theRecordSpellingWrittenInTheClause() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                data Table = List<Int>
                    invariant ok = List.all(x -> Yen { value = 0 }.value <= x, value)
                """);
        assertEquals("check.invariant.construct.named", e.diagnostic().messageKey());
        assertEquals(4, e.diagnostic().region().start().line());
    }

    @Test
    void theCallSpellingWrittenInAHelperTheClauseNames() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                let atLeastZero (x: Int): Bool = Yen(0).value <= x
                data Table = Int
                    invariant ok = atLeastZero(value)
                """);
        assertEquals("check.invariant.construct.named", e.diagnostic().messageKey());
        assertEquals(3, e.diagnostic().region().start().line(),
                "the error is at the construction, which is in the helper");
    }

    @Test
    void theRecordSpellingWrittenInAHelperTheClauseNames() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                let atLeastZero (x: Int): Bool = Yen { value = 0 }.value <= x
                data Table = Int
                    invariant ok = atLeastZero(value)
                """);
        assertEquals("check.invariant.construct.named", e.diagnostic().messageKey());
        assertEquals(3, e.diagnostic().region().start().line());
    }

    /** However many helpers away: the clause arrives at the check with all of them expanded into it,
     *  so the error is at the construction and not at the first helper the clause names. */
    @Test
    void theConstructionIsFoundThroughAChainOfHelpers() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                let inner (x: Int): Bool = Yen(0).value <= x
                let outer (x: Int): Bool = inner(x)
                data Table = Int
                    invariant ok = outer(value)
                """);
        assertEquals("check.invariant.construct.named", e.diagnostic().messageKey());
        assertEquals(3, e.diagnostic().region().start().line(),
                "`inner` holds the construction; `outer` only passes through");
    }

    /** A helper another module published is substituted into the clause the same way, and arrives
     *  already rewritten because that module lowered its own bodies. */
    @Test
    void theConstructionIsFoundInAnImportedHelper() {
        Map<String, String> sources = Map.of(
                "up", """
                        module up exposing ( Yen, atLeastZero )
                        data Yen = Int invariant value >= 0
                        let atLeastZero (x: Int): Bool = Yen(0).value <= x
                        """,
                "down", """
                        module down
                        import up ( atLeastZero )
                        data Table = List<Int>
                            invariant ok = List.all(x -> atLeastZero(x), value)
                        """);
        List<Diagnostic> down = Compiler.diagnoseModules(sources).get("down");
        assertEquals(1, down.size(), () -> "expected one diagnostic, got " + down);
        assertEquals("check.invariant.construct.named", down.get(0).messageKey());
    }

    // --- what the diagnostic says ------------------------------------------------------------

    @Test
    void aNamedClauseIsNamed() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                let atLeastZero (x: Int): Bool = Yen(0).value <= x
                data Table = List<Int>
                    invariant ok = List.all(x -> atLeastZero(x), value)
                """);
        assertEquals(List.of("Table", "Yen", "ok"), List.of(e.diagnostic().args()));
    }

    @Test
    void anUnnamedClauseNamesOnlyTheDeclaration() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                let atLeastZero (x: Int): Bool = Yen(0).value <= x
                data Table = List<Int>
                    invariant List.all(x -> atLeastZero(x), value)
                """);
        assertEquals("check.invariant.construct", e.diagnostic().messageKey());
    }

    /** The construction and the clause that reaches it are two places, so the diagnostic carries
     *  both: the error where the data is built, the clause labelled where the rule is written. */
    @Test
    void theClauseIsLabelledWhereItIsWritten() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                let atLeastZero (x: Int): Bool = Yen(0).value <= x
                data Table = Int
                    invariant ok = atLeastZero(value)
                """);
        assertEquals(1, e.diagnostic().secondary().size());
        assertEquals("check.invariant.construct.here",
                e.diagnostic().secondary().get(0).labelKey());
        assertEquals(5, e.diagnostic().secondary().get(0).region().start().line());
    }

    /**
     * A helper the clause reaches through a combinator is pointed at the combinator rather than at
     * its own body, because expanding a prelude helper stamps the call site on everything it splices
     * in — the caller''s lambda and the helper inlined into it included. That is the inliner''s rule
     * for every diagnostic inside a combinator, not this one''s; it is pinned here so the day it is
     * made finer this test says so.
     */
    @Test
    void aConstructionReachedThroughACombinatorIsPointedAtTheCombinator() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                let atLeastZero (x: Int): Bool = Yen(0).value <= x
                data Table = List<Int>
                    invariant ok = List.all(x -> atLeastZero(x), value)
                """);
        assertEquals("check.invariant.construct.named", e.diagnostic().messageKey());
        assertEquals(5, e.diagnostic().region().start().line());
    }

    /** Written in the clause itself there is one place, and labelling it twice says nothing. */
    @Test
    void aConstructionWrittenInTheClauseIsLabelledOnce() {
        CompileException e = err("""
                module m
                data Yen = Int invariant value >= 0
                data Table = List<Int>
                    invariant ok = List.all(x -> Yen(0).value <= x, value)
                """);
        assertTrue(e.diagnostic().secondary().isEmpty());
    }

    /** A clause is a unit of its own — it is what an attempt answers by name and what discharge
     *  answers about — so a declaration with two wrong clauses says so about both. */
    @Test
    void everyWrongClauseIsReported() {
        Map<String, List<Diagnostic>> found = Compiler.diagnoseModules(Map.of("m", """
                module m
                data Yen = Int invariant value >= 0
                let atLeastZero (x: Int): Bool = Yen(0).value <= x
                data Table = List<Int>
                    invariant low = List.all(x -> atLeastZero(x), value)
                    invariant high = List.all(x -> atLeastZero(x), value)
                """));
        List<String> clauses = found.get("m").stream()
                .filter(d -> "check.invariant.construct.named".equals(d.messageKey()))
                .map(d -> String.valueOf(d.args()[2]))
                .toList();
        assertEquals(List.of("low", "high"), clauses);
    }

    /** Within one clause the first construction is the answer: naming every one of them tells the
     *  author nothing the first does not. */
    @Test
    void oneConstructionIsReportedPerClause() {
        List<Diagnostic> found = Compiler.diagnoseModules(Map.of("m", """
                module m
                data Yen = Int invariant value >= 0
                data Table = List<Int>
                    invariant ok = List.all(x -> Yen(0).value <= x, value) && Yen(1).value >= 0
                """)).get("m");
        assertEquals(1, found.stream()
                .filter(d -> d.messageKey().startsWith("check.invariant.construct")).count());
    }

    // --- the rule is about constructing, not about the newtype --------------------------------

    @Test
    void anInvariantThatOnlyReadsAConstructedValueIsFine() {
        assertFalse(Compiler.compile("""
                module m
                data Yen = Int invariant value >= 0
                data Row = { lo: Yen }
                let ascending (r: Row): Bool = r.lo.value >= 0
                data Table = List<Row>
                    invariant ok = List.all(r -> ascending(r), value)
                """).isEmpty());
    }
}
