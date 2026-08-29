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
 * <p>What is left unread is narrower than it was. A numeric value is named by what computes it, so a
 * call answering a number is a term and its construction is judged; what stays unread is a value the
 * domain does not carry and no rule reaches — a string a call handed back, which no guard states a
 * relation about and no clause folds against.
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
        // `String.startsWith` does not hold of `String.trim(s)` at every `s`, and nothing here says
        // otherwise: the value is a string a call handed back, which nothing states a relation about.
        String source = """
                module demo
                data Tag = String
                    invariant prefixed = String.startsWith("A", value)
                behavior f : (s: String) -> Tag constructs Tag
                let f (s) = Tag(String.trim(s))
                """;
        assertEquals(Verdict.UNREPRESENTABLE, verdictOn("Tag", source),
                "the clause was never asked, so it was not answered");
        assertEquals(0, warnings(source), "and nothing is reported of it");
    }

    @Test
    void aClauseDischargedBesideOneUnreadIsNotTheInvariantProved() {
        // `0 <= 1` folds to true and owes nothing; the prefix clause cannot be read at this value. An
        // invariant is the conjunction of its clauses, so one of them holding is not the invariant.
        String source = """
                module demo
                data Tag = String
                    invariant mixed = 0 <= 1 && String.startsWith("A", value)
                behavior f : (s: String) -> Tag constructs Tag
                let f (s) = Tag(String.trim(s))
                """;
        assertEquals(Verdict.UNREPRESENTABLE, verdictOn("Tag", source),
                "the conjunct left to the run-time check is still left to it");
        assertEquals(0, warnings(source), "and nothing is reported of it");
    }

    @Test
    void oneBranchDischargedBesideOneUnreadIsNotProvedEither() {
        String source = """
                module demo
                data Tag = String
                    invariant prefixed = String.startsWith("A", value)
                behavior f : (s: String, flag: Bool) -> Tag constructs Tag
                let f (s, flag) = Tag(if flag then "A" else String.trim(s))
                """;
        assertEquals(Verdict.UNREPRESENTABLE, verdictOn("Tag", source),
                "`\"A\"` discharges the clause and `String.trim(s)` is not read; together they are"
                        + " the weaker of the two");
        assertEquals(0, warnings(source), "neither reading says the construction may abort");
    }

    /**
     * A call answering a number is read, and what is not known of it is owed rather than skipped.
     *
     * <p>The one that had to be told apart from a discharge, until a value computed by a call became
     * a term of its own. Nothing here knows what {@code Int.max} answers and nothing has to: the two
     * writings of it are one value, which is enough to owe the clause and not enough to settle it.
     */
    @Test
    void aCallAnsweringANumberIsReadAndIsOwedTheClause() {
        String source = """
                module demo
                data Pos = Int
                    invariant positive = value >= 1
                behavior f : (n: Int) -> Pos constructs Pos
                let f (n) = Pos(Int.max(0, n))
                """;
        assertEquals(Verdict.UNKNOWN, verdictOn("Pos", source),
                "`value >= 1` does not hold of `Int.max(0, n)` at n <= 0, and nothing said it does");
        assertEquals(1, warnings(source), "which is what E2011 reports");
    }

    /** And a guard about that same call settles it, which is what makes the warning one an author
     * can answer rather than a limit they are told about. */
    @Test
    void aGuardAboutThatCallSettlesIt() {
        String source = """
                module demo
                data Pos = Int
                    invariant positive = value >= 1
                data TooSmall
                behavior f : (n: Int) -> Pos | TooSmall constructs Pos
                let f (n) = {
                    guard Int.max(0, n) >= 1 else TooSmall
                    Pos(Int.max(0, n))
                }
                """;
        assertEquals(Verdict.PROVED, verdictOn("Pos", source),
                "the guard states of the value exactly what the clause reads of it");
        assertEquals(0, warnings(source), "so nothing is owed");
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
