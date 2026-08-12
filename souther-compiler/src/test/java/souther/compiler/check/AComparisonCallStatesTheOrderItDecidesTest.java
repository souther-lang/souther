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
 * A guard written as the library's {@code compare} against zero states the order it decides.
 *
 * <p>{@code compare(a, b)} answers the sign of the order of its two arguments, so its result
 * standing in a comparison with zero is that same comparison between {@code a} and {@code b} — one
 * account, from which the six relations and both operand orders follow. Without it the same fact
 * settles a construction when written with the operator and settles nothing when written as the
 * call, and which spelling an author reached for decides whether they see a warning they cannot
 * clear.
 *
 * <p>Read off the verdicts: what a guard failed to state and what it stated and could not settle are
 * both reported, and only the first is what this is about.
 */
class AComparisonCallStatesTheOrderItDecidesTest {

    private static final String DECIMALS = """
            module demo

            data Net = Decimal
                invariant value >= 0.0m

            data Refund = { net: Net }
            data FeeTooHigh
            """;

    private static final String INTS = """
            module demo

            data Span = Int
                invariant value >= 0

            data Held = { span: Span }
            data TooSmall
            """;

    private static List<Verdict> verdictsOn(String type, String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } finally {
            InvariantChecker.WATCHING = null;
        }
        List<Verdict> on = said.stream()
                .filter(s -> s.type().equals(type)).map(Said::verdict).toList();
        assertFalse(on.isEmpty(), "no construction of `" + type + "` was checked at all");
        return on;
    }

    private static void reads(String type, Verdict expected, String source) {
        for (Verdict verdict : verdictsOn(type, source)) {
            assertEquals(expected, verdict, "on a construction of `" + type + "`");
        }
    }

    /** A guard over decimals, written both ways, settles the same construction. */
    @Test
    void aDecimalComparisonAgainstZeroSettlesWhatTheOperatorSettles() {
        String written = DECIMALS + """

                behavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh
                    constructs Refund, Net, FeeTooHigh

                let settle (paid, fee) = {
                    guard Decimal.compare(paid, fee) >= 0 else FeeTooHigh
                    Refund { net = Net(paid - fee) }
                }
                """;
        reads("Net", Verdict.PROVED, written);
    }

    /** And settles no more than it says. */
    @Test
    void aDecimalComparisonAgainstZeroSettlesNoMore() {
        String m = DECIMALS + """

                behavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh
                    constructs Refund, Net, FeeTooHigh

                let settle (paid, fee) = {
                    guard Decimal.compare(paid, fee) >= 0 else FeeTooHigh
                    Refund { net = Net(paid - fee - 1.0m) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
    }

    /** The zero on the left is the same guard mirrored. */
    @Test
    void theCallOnTheRightOfTheZero() {
        String m = DECIMALS + """

                behavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh
                    constructs Refund, Net, FeeTooHigh

                let settle (paid, fee) = {
                    guard 0 <= Decimal.compare(paid, fee) else FeeTooHigh
                    Refund { net = Net(paid - fee) }
                }
                """;
        reads("Net", Verdict.PROVED, m);
    }

    /** A strict order states the strict relation: `> 0` is `paid > fee`, which settles the
     * difference as `>= 0` does. */
    @Test
    void aStrictComparison() {
        String m = DECIMALS + """

                behavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh
                    constructs Refund, Net, FeeTooHigh

                let settle (paid, fee) = {
                    guard Decimal.compare(paid, fee) > 0 else FeeTooHigh
                    Refund { net = Net(paid - fee) }
                }
                """;
        reads("Net", Verdict.PROVED, m);
    }

    /** Equality: the two are one value, so their difference is zero. */
    @Test
    void anEqualityComparison() {
        String m = DECIMALS + """

                behavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh
                    constructs Refund, Net, FeeTooHigh

                let settle (paid, fee) = {
                    guard Decimal.compare(paid, fee) == 0 else FeeTooHigh
                    Refund { net = Net(paid - fee) }
                }
                """;
        reads("Net", Verdict.PROVED, m);
    }

    /** The relation the guard denies is the one its departure carries: `< 0` sends the smaller case
     * away, so what is left is `paid >= fee`. */
    @Test
    void aDeniedComparison() {
        String m = DECIMALS + """

                behavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh
                    constructs Refund, Net, FeeTooHigh

                let settle (paid, fee) = {
                    guard Decimal.compare(paid, fee) < 0 else FeeTooHigh
                    Refund { net = Net(fee - paid) }
                }
                """;
        reads("Net", Verdict.PROVED, m);
    }

    /** The same of integers. */
    @Test
    void anIntComparisonAgainstZero() {
        String m = INTS + """

                behavior settle : (hi: Int, lo: Int) -> Held | TooSmall
                    constructs Held, Span, TooSmall

                let settle (hi, lo) = {
                    guard Int.compare(hi, lo) >= 0 else TooSmall
                    Held { span = Span(hi - lo) }
                }
                """;
        reads("Span", Verdict.PROVED, m);
    }

    /** A comparison against something other than zero is not one relation between the arguments —
     * the sign is what the order decides, and a bound on the sign is not a bound on the values. */
    @Test
    void aComparisonAgainstSomethingOtherThanZero() {
        String m = INTS + """

                behavior settle : (hi: Int, lo: Int) -> Held | TooSmall
                    constructs Held, Span, TooSmall

                let settle (hi, lo) = {
                    guard Int.compare(hi, lo) >= 2 else TooSmall
                    Held { span = Span(hi - lo) }
                }
                """;
        reads("Span", Verdict.UNKNOWN, m);
    }

    /**
     * The direction is the library's to say. {@code daysBetween(from, to)} counts forward from its
     * first argument, so a non-negative count says the second is the later — the relation the other
     * way round from what {@code compare} states, read off the same one row.
     */
    @Test
    void aCountForwardIsPositiveWhereTheSecondIsTheGreater() {
        String m = """
                module demo

                data Period = { from: Date, to: Date }
                    invariant notBefore = to >= from

                data Backwards

                behavior span : (from: Date, to: Date) -> Period | Backwards
                    constructs Period, Backwards

                let span (from, to) = {
                    guard Date.daysBetween(from, to) >= 0 else Backwards
                    Period { from = from, to = to }
                }
                """;
        reads("Period", Verdict.PROVED, m);
    }

    /**
     * And a count that truncates decides no order: whole minutes between two date-times are zero
     * wherever they are less than a minute apart, in either direction, so a non-negative count does
     * not say which is the earlier.
     */
    @Test
    void aTruncatedCountDecidesNoOrder() {
        String m = """
                module demo

                data Window = { start: DateTime, end: DateTime }
                    invariant notBefore = end >= start

                data Backwards

                behavior span : (start: DateTime, end: DateTime) -> Window | Backwards
                    constructs Window, Backwards

                let span (start, end) = {
                    guard DateTime.minutesBetween(start, end) >= 0 else Backwards
                    Window { start = start, end = end }
                }
                """;
        reads("Window", Verdict.UNKNOWN, m);
    }

    /**
     * Reading a clause as the order it states must not cost the reading it had. The count itself is a
     * number this check names, and a bound on it is a clause it can read; the two dates it orders are
     * not always both nameable — one of them here is the day after a date — and rewriting the clause
     * into a comparison of those would leave it unreadable, which is a construction dropped from the
     * check where it had been reported. Both readings stand, and the one that answers is taken.
     */
    @Test
    void theOrderReadingDoesNotCostTheBoundOnTheCount() {
        String m = """
                module demo

                data Coverage =
                    { acquiredOn: Date
                    , lostOn: Date
                    }
                    invariant Date.daysBetween(acquiredOn, lostOn) >= 0

                behavior lose : (acquiredOn: Date, separatedOn: Date) -> Coverage
                    constructs Coverage

                let lose (acquiredOn, separatedOn) = {
                    Coverage { acquiredOn = acquiredOn, lostOn = Date.addDays(1, separatedOn) }
                }
                """;
        reads("Coverage", Verdict.UNKNOWN, m);
    }

    /** The model a quantified cap is stated over. */
    private static final String CAPPED = """
            module demo

            data Rate = Decimal
                invariant value >= 0.0m && value <= 0.5m

            data Line = { discount: Decimal }
            data Quote = { rates: List<Rate> }
            data OverCap

            behavior build : (lines: List<Line>) -> Quote | OverCap
                constructs Quote, Rate, OverCap

            let build (lines) = {
                guard withinCaps(lines) else OverCap
                Quote { rates = List.map(r -> Rate(r.discount), lines) }
            }
            """;

    /** What a quantifier states of every element is stated of the one a closure is handed, so a cap
     * written as a comparison call reaches the construction over that element. */
    @Test
    void aCapStatedOfEveryElementAsAComparisonCall() {
        String m = CAPPED + """

                let withinCaps (lines: List<Line>): Bool =
                    List.all(r -> Decimal.compare(r.discount, 0.5m) <= 0
                              && Decimal.compare(r.discount, 0.0m) >= 0, lines)
                """;
        reads("Rate", Verdict.PROVED, m);
    }

    /** And a cap that leaves room past the clause does not: the relation the call states is the one
     * it was written with, not the one the type wanted. */
    @Test
    void aCapLooserThanTheClauseSettlesNothing() {
        String m = CAPPED + """

                let withinCaps (lines: List<Line>): Bool =
                    List.all(r -> Decimal.compare(r.discount, 0.6m) <= 0
                              && Decimal.compare(r.discount, 0.0m) >= 0, lines)
                """;
        reads("Rate", Verdict.UNKNOWN, m);
    }

    /** A clause written as a comparison call and a guard written with the operator are one fact:
     * the reading is the same at both ends, so which end wrote which spelling does not matter. */
    @Test
    void aClauseWrittenAsAComparisonMeetsAGuardWrittenAsAnOperator() {
        String m = """
                module demo

                data Ordered = { low: Int, high: Int }
                    invariant inOrder = Int.compare(high, low) >= 0

                data NotOrdered

                behavior order : (a: Int, b: Int) -> Ordered | NotOrdered
                    constructs Ordered, NotOrdered

                let order (a, b) = {
                    guard a >= b else NotOrdered
                    Ordered { low = b, high = a }
                }
                """;
        reads("Ordered", Verdict.PROVED, m);
    }
}
