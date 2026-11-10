package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.UndividedPosition;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A sum, a difference or a product of decimals that decides nothing changes nothing of what the
 * comparison after it says. Each behavior here is the control with one such operation put before
 * the comparison, and its report is the control's.
 */
class ADecimalOperationTheRelationDoesNotReadLeavesThePlacesItReadsReachedTest {

    private static final String MODEL = """
            module probe

            data Amount = Decimal
                invariant value >= 0.0m

            data Pair = { a: Amount, b: Amount }

            behavior control : (p: Pair) -> Int
            let control (p) = {
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior difference : (p: Pair) -> Int
            let difference (p) = {
                let diff = Decimal.subtract(p.a.value, p.b.value)
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior sum : (p: Pair) -> Int
            let sum (p) = {
                let total = Decimal.add(p.a.value, p.b.value)
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior minus : (p: Pair) -> Int
            let minus (p) = {
                let diff = p.a.value - p.b.value
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior times : (p: Pair) -> Int
            let times (p) = {
                let product = Decimal.multiply(p.a.value, p.b.value)
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior chained : (p: Pair) -> Int
            let chained (p) = {
                let spread = Decimal.multiply(Decimal.add(p.a.value, 1.50m), p.b.value)
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            data Invoice = { dueOn: Date, gross: Decimal }
            data Rep = { current: Decimal, overdue30: Decimal }

            let daysLate (invoice: Invoice, today: Date): Int =
                Date.daysBetween(invoice.dueOn, today)

            let inBand (invoices: List<Invoice>, today: Date, from: Int, to: Int): List<Invoice> =
                List.filter(i -> daysLate(i, today) >= from && daysLate(i, today) < to, invoices)

            let addedUp (invoices: List<Invoice>): Decimal =
                List.foldRight((i, acc) -> Decimal.add(acc, i.gross), 0.0m, invoices)

            let counted (invoices: List<Invoice>): Decimal =
                Decimal.fromInt(List.length(invoices))

            behavior ageingControl : (invoices: List<Invoice>, today: Date) -> Rep
                constructs Rep
            let ageingControl (invoices, today) = Rep {
                current = counted(inBand(invoices, today, 0 - 3650, 1)),
                overdue30 = counted(inBand(invoices, today, 1, 31))
            }

            behavior ageing : (invoices: List<Invoice>, today: Date) -> Rep
                constructs Rep
            let ageing (invoices, today) = Rep {
                current = addedUp(inBand(invoices, today, 0 - 3650, 1)),
                overdue30 = addedUp(inBand(invoices, today, 1, 31))
            }
            """;

    private static Map<String, UndividedPosition.Reason> reasonsOf(
            Map<String, PartitionEvidence> evidence, String behavior) {
        Map<String, UndividedPosition.Reason> byPlace = new LinkedHashMap<>();
        evidence.get(behavior).notRead().forEach(each -> byPlace.put(each.at(), each.reason()));
        return byPlace;
    }

    @Test
    void aDecimalOperationThatDecidesNothingLeavesTheReportAsItWas() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> evidence =
                compilation.db().ask(new Adequacy.Coverage("probe")).value();
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), compilation.errors().toString());

        for (String behavior : List.of("difference", "sum", "minus", "times", "chained")) {
            assertEquals(reasonsOf(evidence, "control"), reasonsOf(evidence, behavior), behavior);
        }
        assertEquals(reasonsOf(evidence, "ageingControl"), reasonsOf(evidence, "ageing"));
    }
}
