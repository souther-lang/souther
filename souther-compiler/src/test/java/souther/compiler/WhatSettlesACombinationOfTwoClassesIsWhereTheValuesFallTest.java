package souther.compiler;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A combination of two classes is settled by where the values fall, and by nothing about the run.
 *
 * <p>The two criteria are asymmetric on purpose. A combination of the body's decisions is a meeting
 * a run either reached or did not, so what settles it is the account of the run; a combination of
 * two classes is the criterion of a behavior whose decisions meet nowhere — and of one with no body
 * at all — so there is no meeting for a run to have reached, and a row's values are the whole of
 * the evidence there is.
 *
 * <p>Which is what makes the fallback usable where it is the criterion. Asking for a run there
 * would carry the interaction's evidence requirement into the one case it was never about.
 */
class WhatSettlesACombinationOfTwoClassesIsWhereTheValuesFallTest {

    /** Two positions the body tells apart, whose decisions meet nowhere. */
    private static final String MODEL = """
            module example.values

            data Domestic
            data Overseas
            data Kind = Domestic | Overseas
            data Amount = Int
                invariant value >= 0
            data Request = { kind: Kind, cost: Amount }
            data Ok = { n: Int }
            data Waiting = { n: Int }

            behavior submit : (request: Request) -> Ok | Waiting
                constructs Ok, Waiting

            let submit (request) = match request.kind with
                | Domestic -> {
                    guard request.cost.value <= 100 else Waiting { n = 1 }
                    Ok { n = 0 }
                }
                | Overseas -> Ok { n = 2 }
            """;

    private static final String EVERY_COMBINATION = """
            example submit
                | (Request { kind = Domestic, cost = Amount(50) })  -> Ok { n = 0 }
                | (Request { kind = Domestic, cost = Amount(500) }) -> Waiting { n = 1 }
                | (Request { kind = Overseas, cost = Amount(50) })  -> Ok { n = 2 }
                | (Request { kind = Overseas, cost = Amount(500) }) -> Ok { n = 2 }
            """;

    /**
     * Rows that reach every combination leave nothing owed, at a level that watches no run.
     *
     * <p>{@code witness} reads what the rows the compile already ran established and records
     * nothing about where a run went. The combinations are settled all the same: where each row's
     * values fall is what the classifier answers, and it answers it without an account.
     */
    @Test
    void aCombinationIsSettledWithoutAnAccountOfTheRun() {
        Compilation compilation = Compilation.ofSource(MODEL + EVERY_COMBINATION, "Main");
        compilation.measure(Adequacy.Level.WITNESS);
        compilation.answerEverything();

        assertEquals(List.of(), gapsOf(compilation),
                () -> "the rows sit in every combination, and no run was watched: "
                        + AdequacyReport.of(compilation).human(
                                souther.compiler.diag.SourceRendering
                                        .namedByIdentity(compilation.texts())));
    }

    /**
     * And one the rows do not reach is a gap at that level, not something left undecided.
     *
     * <p>The other half: what makes a combination undecided is a value nothing could classify, and
     * a build that watched no run has classified every value it was given.
     */
    @Test
    void aCombinationTheRowsDoNotReachIsAGapWithoutOne() {
        Compilation compilation = Compilation.ofSource(MODEL + """
                example submit
                    | (Request { kind = Domestic, cost = Amount(50) })  -> Ok { n = 0 }
                    | (Request { kind = Domestic, cost = Amount(500) }) -> Waiting { n = 1 }
                    | (Request { kind = Overseas, cost = Amount(50) })  -> Ok { n = 2 }
                """, "Main");
        compilation.measure(Adequacy.Level.WITNESS);
        compilation.answerEverything();

        List<Adequacy.Finding> gaps = gapsOf(compilation);
        assertEquals(1, gaps.size(), () -> "the combination nothing is in: " + gaps);
        assertTrue(gaps.getFirst().isAdequacyGap(),
                "a build may refuse over it: every value was classified");
        assertFalse(gaps.getFirst().weakenedBy().isEmpty()
                        && gaps.getFirst().disposition() != Adequacy.Finding.Disposition.REFUSED,
                "and what it rests on is the classification alone");
    }

    private static List<Adequacy.Finding> gapsOf(Compilation compilation) {
        List<Adequacy.Finding> findings =
                compilation.db().ask(new Adequacy.Findings("example.values")).value();
        return findings == null ? List.of() : findings.stream()
                .filter(each -> each.kind() == Adequacy.Kind.PAIR_UNCOVERED)
                .toList();
    }
}
