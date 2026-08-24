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
 * What this check makes of a clause counting two dates apart, over the model #949 is written about.
 *
 * <p>Here because one reading now has two readers. {@code AffineForms.composed} is read by the
 * discharge check and by the partition, and what an operation answers in what it was given is
 * declared once for both — so a date is now a carrier the composition walks, and the operations over
 * dates say what they answer in it. The partition's side of that is pinned where it is measured; this
 * check's side was measured by hand, and a shared reader with one pinned reader moves the other with
 * nothing failing.
 *
 * <p>Every verdict below is what was read at {@code c9ef497f} — the develop these declarations
 * arrived on — and is unchanged by them. That is the claim: the semantics widened and this check's
 * answers did not.
 *
 * <p>What decides them is what this check can carry and not what the library declares. Its
 * arithmetic is over the numbers a model wrote, and a date is not one
 * ({@link DischargeRules#formOperationsThisCarries}), so a clause is discharged here through the
 * measure that counts two dates apart — which is what a shift states ({@code Date.addDays}) and what
 * a guard writing the clause states of itself. The same statement spelled as two shifted dates
 * compared is not carried, and the two spellings coming to one answer is the partition's, where a
 * border is drawn over the numbers themselves.
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
     * And the same statement spelled as a comparison of two shifted dates does not, which is what
     * this check carrying no date says. The two spellings are one statement — the partition draws one
     * border for both — and here they come to different answers, so this is the boundary of what the
     * declarations bought and not an incidental gap.
     */
    @Test
    void theSameStatementSpelledAsShiftedDatesComparedDoesNot() {
        reads(Verdict.UNKNOWN, MODEL + """
                data TooWide
                behavior makeSpan : (a: Date, n: Int) -> Span | TooWide constructs Span
                let makeSpan (a, n) =
                    if Date.addDays(30, a) >= Date.addDays(n, a) then
                        Span { from = a, to = Date.addDays(n, a) }
                    else TooWide
                """);
    }

    /** A shift by months moves a date by no number of days, so the measure says nothing of it. */
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
