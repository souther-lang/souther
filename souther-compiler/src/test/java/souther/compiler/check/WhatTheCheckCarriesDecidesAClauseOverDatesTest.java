package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * One arithmetic over dates is read one way, however a clause spells it.
 *
 * <p>Here because one reading has two readers. {@code AffineForms.composed} is read by the discharge
 * check and by the partition, and what an operation answers in what it was given is declared once for
 * both. So a capability pinned per reader is a capability two readers can come apart on, and what is
 * held here is that they do not.
 *
 * <p><b>What this check can carry is asked of the carrier.</b> A carrier that counts has an internal
 * coordinate this reasons over — a date's is its day — and reasoning over it does not make the date a
 * number the model wrote. Asked of whether the type is such a number, this check would hold a second
 * capability beside the term reader's, and the two spellings below would answer apart: one statement
 * carried because a shift writes it, and the same statement refused because the count writes it.
 *
 * <p>What the spellings have in common is the relation; what differs is only which operation writes
 * it down.
 */
class WhatTheCheckCarriesDecidesAClauseOverDatesTest {

    /** #949's model, as the issue writes it. */
    private static final String MODEL = """
            module demo
            data Span = { from: Date, to: Date }
                invariant within = Date.daysBetween(from, to) <= 30
            """;

    @Test
    void aShiftInsideTheBoundIsDischargedThroughTheMeasureThatCountsIt() {
        reads(Verdict.PROVED, MODEL + """
                behavior makeSpan : (d: Date) -> Span constructs Span
                let makeSpan (d) = Span { from = d, to = Date.addDays(10, d) }
                """);
    }

    @Test
    void aShiftPastTheBoundIsRefutedOnTheValuesAlone() {
        reads(Verdict.REFUTED_ALONE, MODEL + """
                behavior makeSpan : (d: Date) -> Span constructs Span
                let makeSpan (d) = Span { from = d, to = Date.addDays(40, d) }
                """);
    }

    @Test
    void twoDatesWithNothingStatedBetweenThemLeaveTheClauseUnproven() {
        reads(Verdict.UNKNOWN, MODEL + """
                behavior makeSpan : (a: Date, b: Date) -> Span constructs Span
                let makeSpan (a, b) = Span { from = a, to = b }
                """);
    }

    /** A guard writing the clause states it of the values the construction is over. */
    @Test
    void theClauseInTheGuardDischargesIt() {
        reads(Verdict.PROVED, MODEL + """
                data TooWide
                behavior makeSpan : (a: Date, b: Date) -> Span | TooWide constructs Span
                let makeSpan (a, b) =
                    if Date.daysBetween(a, b) <= 30 then Span { from = a, to = b }
                    else TooWide
                """);
    }

    /**
     * And the same statement spelled as a comparison of two shifted dates discharges it too.
     *
     * <p>The pair of the one above, and the whole of what this file is for. The two are one
     * statement about one relation, and a reader answering them apart would be answering about which
     * operation an author reached for. Nothing here is about a date being a number: what both
     * spellings are read over is the day, which is the carrier's coordinate and is a number of its
     * own.
     */
    @Test
    void theSameStatementSpelledAsShiftedDatesComparedDischargesItToo() {
        reads(Verdict.PROVED, MODEL + """
                data TooWide
                behavior makeSpan : (a: Date, n: Int) -> Span | TooWide constructs Span
                let makeSpan (a, n) =
                    if Date.addDays(30, a) >= Date.addDays(n, a) then
                        Span { from = a, to = Date.addDays(n, a) }
                    else TooWide
                """);
    }

    /**
     * A shift by months moves a date by no number of days, so the measure says nothing of it.
     *
     * <p><b>Which is what says a date is no number.</b> What this check reasons over is the day a
     * date counts, and an operation moving a date by something other than a count of days states no
     * form in that day — so there is nothing here to carry. A reading that made dates into whole
     * numbers would have nothing to stop at.
     */
    @Test
    void aShiftByMonthsLeavesTheClauseUnproven() {
        reads(Verdict.UNKNOWN, MODEL + """
                behavior makeSpan : (d: Date) -> Span constructs Span
                let makeSpan (d) = Span { from = d, to = Date.addMonths(1, d) }
                """);
    }

    /** The verdicts this check reached on constructions of {@code Span}, and that it reached one:
     *  a construction nothing judged would otherwise be read as a construction nothing is owed on. */
    private static void reads(Verdict expected, String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } catch (souther.compiler.diag.CompileException refused) {
            // A construction the values refute is reported, and the verdict saying so was reached
            // before it was. Any other refusal is this test's own program being wrong, and
            // swallowing it would leave `no construction was judged` standing for `it did not
            // compile`.
            if (!expected.refuted()) {
                throw refused;
            }
        } finally {
            InvariantChecker.WATCHING = null;
        }
        List<Verdict> reached = said.stream().map(Said::verdict).toList();
        assertFalse(reached.isEmpty(), "no construction of Span was judged at all");
        assertEquals(List.of(expected), reached);
    }
}
