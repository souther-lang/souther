package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A construction the check could not read and one it discharged are both silent, and they are not the
 * same answer.
 *
 * <p>Held together they read as one: an author who writes a construction over something outside the
 * fragment sees the same nothing as one whose guards discharged it, and takes the silence for a proof
 * that was never attempted. Nothing reports the difference and this does not change that, so it is
 * read off the verdicts rather than off the diagnostics — a difference no test can reach is one that
 * stops being true without anything failing.
 *
 * <p>What made it worth telling apart is {@code Int.max}: it keeps its call where the check reads the
 * body, a call is not a term any clause is read against, and a construction over one is silent
 * however plainly it violates. That silence read as a discharge is what {@code #409} reported.
 */
class WhatTheCheckCouldNotReadIsNotWhatItProvedTest {

    /** How the check came out on each construction of {@code source}. */
    private static List<Said> verdictsIn(String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } finally {
            InvariantChecker.WATCHING = null;
        }
        assertFalse(said.isEmpty(), "nothing was checked, so nothing here is being held to anything");
        return said;
    }

    private static Verdict verdictOn(String type, String source) {
        return verdictsIn(source).stream()
                .filter(s -> s.type().equals(type)).findFirst().orElseThrow().verdict();
    }

    private static long warnings(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    @Test
    void aValueTheCheckCannotReadIsNotADischarge() {
        // `value >= 1` does not hold of `Int.max(0, n)` at n <= 0, and nothing here says otherwise.
        String source = """
                module demo
                data Pos = Int
                    invariant positive = value >= 1
                behavior f : (n: Int) -> Pos constructs Pos
                let f (n) = Pos(Int.max(0, n))
                """;
        assertEquals(Verdict.UNREPRESENTABLE, verdictOn("Pos", source),
                "the clause was never asked, so it was not answered");
        assertEquals(0, warnings(source), "and nothing is reported of it");
    }

    @Test
    void aClauseDischargedBesideOneUnreadIsNotTheInvariantProved() {
        // `0 <= 1` folds to true and owes nothing; `value >= 1` cannot be read at this value. An
        // invariant is the conjunction of its clauses, so one of them holding is not the invariant.
        String source = """
                module demo
                data Pos = Int
                    invariant mixed = 0 <= 1 && value >= 1
                behavior f : (n: Int) -> Pos constructs Pos
                let f (n) = Pos(Int.max(0, n))
                """;
        assertEquals(Verdict.UNREPRESENTABLE, verdictOn("Pos", source),
                "the conjunct left to the run-time check is still left to it");
        assertEquals(0, warnings(source), "and nothing is reported of it");
    }

    @Test
    void oneBranchDischargedBesideOneUnreadIsNotProvedEither() {
        String source = """
                module demo
                data Yen = Int
                    invariant nonNegative = value >= 0
                behavior f : (n: Int, flag: Bool) -> Yen constructs Yen
                let f (n, flag) = Yen(if flag then 0 else Int.max(0, n))
                """;
        assertEquals(Verdict.UNREPRESENTABLE, verdictOn("Yen", source),
                "`0` discharges the clause and `Int.max(0, n)` is not read; together they are the"
                        + " weaker of the two");
        assertEquals(0, warnings(source), "neither reading says the construction may abort");
    }

    @Test
    void aDischargeIsStillADischarge() {
        assertEquals(Verdict.PROVED, verdictOn("Yen", """
                module demo
                data Yen = Int
                    invariant nonNegative = value >= 0
                behavior f : (n: Int) -> Yen constructs Yen
                let f (n) = Yen(if n < 0 then 0 else n)
                """),
                "both branches are non-negative under the condition");
    }

    @Test
    void aValueTheCheckCanReadAndCannotProveIsStillReported() {
        String source = """
                module demo
                data Pos = Int
                    invariant positive = value >= 1
                behavior f : (n: Int) -> Pos constructs Pos
                let f (n) = Pos(n)
                """;
        assertEquals(Verdict.UNKNOWN, verdictOn("Pos", source),
                "`n` is a term, and nothing said it is at least one");
        assertEquals(1, warnings(source), "which is what E2011 reports");
    }
}
