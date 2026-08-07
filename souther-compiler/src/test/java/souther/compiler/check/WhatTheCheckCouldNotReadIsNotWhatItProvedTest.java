package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A construction the check could not read and one it discharged are both silent, and they are not the
 * same answer.
 *
 * <p>Held together they read as one: an author who writes a construction over something outside the
 * fragment sees the same nothing as one whose guards discharged it, and takes the silence for a proof
 * that was never attempted. Nothing reports the difference today and this does not change that. What
 * is held here is where the two answers meet — a construction over a conditional is read once per
 * branch and the two readings are answered together, and a discharge on one branch beside an unread
 * value on the other is still nothing to report.
 *
 * <p>The stdlib shapes are the ones that made this worth telling apart: {@code Int.max} keeps its call
 * where the check reads the body, and a call is not a term any clause can be read against, so a
 * construction over one is silent however plainly it violates.
 */
class WhatTheCheckCouldNotReadIsNotWhatItProvedTest {

    private static long warnings(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    @Test
    void oneBranchDischargedBesideOneUnreadIsStillSilent() {
        // `0` discharges the clause; `Int.max(0, n)` is a call, and no clause is read against it.
        assertEquals(0, warnings("""
                module demo
                data Yen = Int
                    invariant nonNegative = value >= 0
                behavior f : (n: Int, flag: Bool) -> Yen constructs Yen
                let f (n, flag) = Yen(if flag then 0 else Int.max(0, n))
                """),
                "neither reading says the construction may abort, so neither does the answer");
    }

    @Test
    void aConstructionOverAnUnreadValueIsSilentWhateverItsClauseSays() {
        // `value >= 1` does not hold of `Int.max(0, n)` at n <= 0. The check says nothing because it
        // cannot read the value, not because it settled the clause.
        assertEquals(0, warnings("""
                module demo
                data Pos = Int
                    invariant positive = value >= 1
                behavior f : (n: Int) -> Pos constructs Pos
                let f (n) = Pos(Int.max(0, n))
                """),
                "the run-time check is the whole of the enforcement here");
    }

    @Test
    void aValueTheCheckCanReadAndCannotProveIsStillReported() {
        assertEquals(1, warnings("""
                module demo
                data Pos = Int
                    invariant positive = value >= 1
                behavior f : (n: Int) -> Pos constructs Pos
                let f (n) = Pos(n)
                """),
                "`n` is a term, and nothing said it is at least one");
    }
}
