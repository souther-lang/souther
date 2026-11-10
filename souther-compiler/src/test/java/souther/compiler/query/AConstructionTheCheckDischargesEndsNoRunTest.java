package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.UndividedPosition;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A construction the check of the declarations discharges ends no run, whatever shape the number it
 * is made of has, so a comparison after it is read as it is without it. One it does not discharge
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

            behavior refused : (invoices: List<Invoice>, today: Date) -> Decimal
                constructs Amount
            let refused (invoices, today) = {
                let first = Amount(Decimal.subtract(totalOf(lateBy(invoices, today, 0)), 1.0m))
                Decimal.add(first.value, totalOf(lateBy(invoices, today, 30)))
            }
            """;

    private static Map<String, UndividedPosition.Reason> reasonsOf(
            Map<String, PartitionEvidence> evidence, String behavior) {
        Map<String, UndividedPosition.Reason> byPlace = new LinkedHashMap<>();
        evidence.get(behavior).notRead().forEach(each -> byPlace.put(each.at(), each.reason()));
        return byPlace;
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
        assertTrue(reasonsOf(evidence, "refused").containsValue(
                UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE),
                reasonsOf(evidence, "refused").toString());
    }
}
