package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.UndividedPosition;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction the check of the declarations discharges ends no run, whatever shape the number it
 * is made of has and whether it names a value the module defines, so a comparison after it is read
 * as it is without it. One it does not discharge
 * can end a run, and a comparison after it is not shown reached.
 */
class AConstructionTheCheckDischargesEndsNoRunTest {

    private static final String MODEL = """
            module probe

            data Amount = Decimal
                invariant value >= 0.0m

            data Invoice = { dueOn: Date, gross: Amount }

            let totalOf (invoices: List<Invoice>): Decimal =
                List.foldRight((i, acc) -> Decimal.add(acc, i.gross.value), 0.0m, invoices)

            let lateBy (invoices: List<Invoice>, today: Date, days: Int): List<Invoice> =
                List.filter(i -> Date.daysBetween(i.dueOn, today) > days, invoices)

            behavior control : (invoices: List<Invoice>, today: Date) -> Decimal
            let control (invoices, today) = {
                let first = totalOf(lateBy(invoices, today, 0))
                Decimal.add(first, totalOf(lateBy(invoices, today, 30)))
            }

            behavior discharged : (invoices: List<Invoice>, today: Date) -> Decimal
                constructs Amount
            let discharged (invoices, today) = {
                let first = Amount(totalOf(lateBy(invoices, today, 0)))
                Decimal.add(first.value, totalOf(lateBy(invoices, today, 30)))
            }

            let eight = Amount(8.0m)

            data Kind = Ordinary | Holiday
            data Day = { worked: Amount, kind: Kind }

            let ordinaryOn (d: Day): Amount =
                match d.kind with
                    | Holiday -> Amount(0.0m)
                    | Ordinary -> if d.worked > eight then eight else d.worked

            let sumOf (f: (Day) -> Amount, days: List<Day>): Amount =
                Amount(List.sum(List.map(d -> f(d).value, days)))

            behavior tally : (days: List<Day>) -> Amount
                constructs Amount
            let tally (days) = {
                let total = sumOf(d -> ordinaryOn(d), days)
                if total.value > 60.0m then total else eight
            }

            behavior refused : (invoices: List<Invoice>, today: Date) -> Decimal
                constructs Amount
            let refused (invoices, today) = {
                let first = Amount(Decimal.subtract(totalOf(lateBy(invoices, today, 0)), 1.0m))
                Decimal.add(first.value, totalOf(lateBy(invoices, today, 30)))
            }
            """;

    /** What a behavior leaves unread, each place once for every report of it. */
    private static List<String> reasonsOf(Map<String, PartitionEvidence> evidence,
                                          String behavior) {
        return evidence.get(behavior).notRead().stream()
                .map(each -> each.at() + ": " + each.reason()).sorted().toList();
    }

    @Test
    void aConstructionIsReachedPastOnlyWhereTheCheckDischargesIt() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), compilation.errors().toString());

        assertEquals(reasonsOf(evidence, "control"), reasonsOf(evidence, "discharged"));
        assertTrue(evidence.containsKey("tally"));
        assertTrue(reasonsOf(evidence, "refused").stream().anyMatch(each -> each.endsWith(
                ": " + UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)),
                reasonsOf(evidence, "refused").toString());
    }
}
