package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A sum, a difference or a product of decimals that decides nothing changes nothing of what the
 * comparison after it says, whatever the operands are written as. Each behavior here is the control
 * with one such operation put before the comparison, and its report is the control's; and a side of
 * a comparison that negates a place is read as the side that is the place.
 */
class ADecimalOperationTheRelationDoesNotReadLeavesThePlacesItReadsReachedTest {

    private static final String MODEL = """
            module probe

            data Amount = Decimal
                invariant value >= 0.0m

            data Pair = { a: Amount, b: Amount }

            data Loose = { a: Decimal, b: Decimal }

            behavior plainSide : (p: Loose) -> Int
            let plainSide (p) = {
                let sign = Decimal.compare(Decimal.add(p.a, p.b), 0.0m)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior negatedSide : (p: Loose) -> Int
            let negatedSide (p) = {
                let sign = Decimal.compare(Decimal.add(-p.a, p.b), 0.0m)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior controlTruth : (p: Pair) -> Bool
            let controlTruth (p) = Decimal.compare(p.a.value, p.b.value) == 0

            behavior differenceTruth : (p: Pair) -> Bool
            let differenceTruth (p) = {
                let diff = Decimal.subtract(p.a.value, p.b.value)
                Decimal.compare(p.a.value, p.b.value) == 0
            }

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

            behavior negated : (p: Pair) -> Int
            let negated (p) = {
                let total = Decimal.add(-p.a.value, p.b.value)
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior widened : (p: Pair, n: Int) -> Int
            let widened (p, n) = {
                let total = Decimal.add(Decimal.fromInt(n), p.a.value)
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior chosen : (p: Pair) -> Int
            let chosen (p) = {
                let total = Decimal.multiply(Decimal.max(p.a.value, p.b.value), p.a.value)
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior rounded : (p: Pair) -> Int
            let rounded (p) = {
                let total = Decimal.add(Decimal.round(2, HALF_UP, p.a.value), p.b.value)
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior absolute : (p: Pair) -> Int
            let absolute (p) = {
                let size = Decimal.add(Decimal.abs(p.a.value), Decimal.abs(Decimal.round(2, HALF_UP,
                    p.b.value)))
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior quotient : (p: Pair) -> Int
            let quotient (p) = {
                let size = match Decimal.divide(p.a.value, p.b.value, 2, HALF_UP) with
                    | Decimal as q -> Decimal.multiply(q, Decimal.add(q, p.a.value))
                    | DivisionByZero -> 0.0m
                let sign = Decimal.compare(p.a.value, p.b.value)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            data Tuned = { a: Decimal, b: Decimal, s: Int }

            behavior quotientAtAnInputScale : (p: Tuned) -> Int
            let quotientAtAnInputScale (p) = {
                let size = match Decimal.divide(p.a, p.b, p.s, HALF_UP) with
                    | Decimal as q -> Decimal.add(q, p.a)
                    | DivisionByZero -> 0.0m
                let sign = Decimal.compare(p.a, p.b)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }

            behavior quotientAtAScaleNoRoomHolds : (p: Tuned) -> Int
            let quotientAtAScaleNoRoomHolds (p) = {
                let size = match Decimal.divide(p.a, p.b, 2147483647, HALF_UP) with
                    | Decimal as q -> Decimal.add(q, p.a)
                    | DivisionByZero -> 0.0m
                let sign = Decimal.compare(p.a, p.b)
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

    /** What a behavior leaves unread, each place once for every report of it. */
    private static List<String> reasonsOf(Map<String, PartitionEvidence> evidence,
                                          String behavior) {
        return evidence.get(behavior).notRead().stream()
                .map(each -> each.at() + ": " + each.reason()).sorted().toList();
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

        for (String behavior : List.of("difference", "sum", "minus", "times", "chained", "negated",
                "widened", "chosen", "rounded", "absolute", "quotient")) {
            assertEquals(reasonsOf(evidence, "control"), reasonsOf(evidence, behavior), behavior);
        }
        assertEquals(reasonsOf(evidence, "controlTruth"), reasonsOf(evidence, "differenceTruth"));
        assertEquals(reasonsOf(evidence, "plainSide"), reasonsOf(evidence, "negatedSide"));
        // A quotient at a scale the call does not write, or at one no room holds, can end a run.
        for (String behavior : List.of("quotientAtAnInputScale", "quotientAtAScaleNoRoomHolds")) {
            assertTrue(reasonsOf(evidence, behavior).stream().anyMatch(each -> each.endsWith(
                    "RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE")), behavior);
        }
        assertEquals(reasonsOf(evidence, "ageingControl"), reasonsOf(evidence, "ageing"));
    }
}
