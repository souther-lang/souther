package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.Arguments;
import org.junit.jupiter.params.provider.MethodSource;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A guard written as the library's {@code compare} states the order it decides, wherever the
 * condition settles which side of nought the answer falls on.
 *
 * <p>{@code compare(a, b)} answers the sign of the order of its two arguments, so a condition
 * leaving that sign on one side of nought is the same comparison between {@code a} and {@code b} —
 * one account, from which the six relations and both operand orders follow. Without it the same fact
 * settles a construction when written with the operator and settles nothing when written as the
 * call, and which spelling an author reached for decides whether they see a warning they cannot
 * clear.
 *
 * <p>Which side the condition leaves is worked out from what the operation declares of its answer
 * and what the condition says, together ({@code Conditions.standsToNought}). A comparison against
 * nought is the common way to write one and is not the reading: {@code compare(a, b) >= 1} settles
 * the same side, and over numbers that step so does {@code > -1}.
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
        List<Verdict> on = checked(type, source);
        assertFalse(on.isEmpty(), "no construction of `" + type + "` was checked at all");
        return on;
    }

    /** The verdicts on constructions of {@code type}, which is empty where the program builds none
     *  the check reaches. */
    private static List<Verdict> checked(String type, String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } catch (souther.compiler.diag.CompileException refused) {
            // A construction the guards refute is an error, and the verdict that says so was reached
            // before it was raised. What is asked here is which verdict, not whether it compiles.
        } finally {
            InvariantChecker.WATCHING = null;
        }
        return said.stream().filter(s -> s.type().equals(type)).map(Said::verdict).toList();
    }

    private static void reads(String type, Verdict expected, String source) {
        for (Verdict verdict : verdictsOn(type, source)) {
            assertEquals(expected, verdict, "on a construction of `" + type + "`");
        }
    }

    /**
     * The six relations, each written with the call on either side of the zero.
     *
     * <p>What is held is the whole account at once: the relation the guard states is the one written,
     * taken between the two arguments, and writing the zero on the other side states the same fact
     * mirrored. So the two spellings of a row answer alike, and what they answer is what that
     * relation gives a construction of `paid - fee` — settled where the guard puts `paid` at or above
     * `fee`, refuted where it puts it below, and unsettled where it leaves both open.
     */
    @ParameterizedTest(name = "{0} 0 and 0 {1}")
    @MethodSource("relations")
    void eachRelationOnEitherSideOfTheZero(String written, String mirrored, Verdict expected) {
        reads("Net", expected, guarded("Decimal.compare(paid, fee) " + written + " 0"));
        reads("Net", expected, guarded("0 " + mirrored + " Decimal.compare(paid, fee)"));
    }

    private static List<Arguments> relations() {
        return List.of(
                Arguments.of(">=", "<=", Verdict.PROVED),
                Arguments.of(">", "<", Verdict.PROVED),
                Arguments.of("==", "==", Verdict.PROVED),
                Arguments.of("/=", "/=", Verdict.UNKNOWN),
                Arguments.of("<=", ">=", Verdict.UNKNOWN),
                Arguments.of("<", ">", Verdict.REFUTED_NOT_ALONE));
    }

    /** The model those are read in: a difference the guard is what settles. */
    private static String guarded(String condition) {
        return DECIMALS
                + "\nbehavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh\n"
                + "    constructs Refund, Net\n\n"
                + "let settle (paid, fee) = {\n"
                + "    guard " + condition + " else FeeTooHigh\n"
                + "    Refund { net = Net(paid - fee) }\n"
                + "}\n";
    }

    /** What the table above settles, it settles no more of. */
    @Test
    void aDecimalComparisonAgainstZeroSettlesNoMore() {
        String m = DECIMALS + """

                behavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh
                    constructs Refund, Net

                let settle (paid, fee) = {
                    guard Decimal.compare(paid, fee) >= 0 else FeeTooHigh
                    Refund { net = Net(paid - fee - 1.0m) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
    }

    /** The relation the guard denies is the one its departure carries: `< 0` sends the smaller case
     * away, so what is left is `paid >= fee`. */
    @Test
    void aDeniedComparison() {
        String m = DECIMALS + """

                behavior settle : (paid: Decimal, fee: Decimal) -> Refund | FeeTooHigh
                    constructs Refund, Net

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
                    constructs Held, Span

                let settle (hi, lo) = {
                    guard Int.compare(hi, lo) >= 0 else TooSmall
                    Held { span = Span(hi - lo) }
                }
                """;
        reads("Span", Verdict.PROVED, m);
    }

    /**
     * And only that way round. The guard puts {@code hi} at or above {@code lo}, so the difference
     * taken the other way is at or below zero and a {@code Span} built from it is not proved. A row
     * read backwards proves it, from a relation between the two the program never states — which is
     * the one failure of this table that reaches a construction rather than only losing one.
     */
    @Test
    void theDifferenceTakenTheOtherWayIsNotProved() {
        String m = INTS + """

                behavior settle : (hi: Int, lo: Int) -> Held | TooSmall
                    constructs Held, Span

                let settle (hi, lo) = {
                    guard Int.compare(hi, lo) >= 0 else TooSmall
                    Held { span = Span(lo - hi) }
                }
                """;
        reads("Span", Verdict.UNKNOWN, m);
    }

    /**
     * A comparison that bounds how far the answer is from nought and not which side it falls says
     * nothing about the order. What decides is what the condition leaves, and this one leaves both
     * sides.
     *
     * <p>Over a count, which is where a comparison like this is still open: what the language's own
     * comparisons answer is one of three numbers, so few conditions on one leave both sides.
     */
    @Test
    void aComparisonThatBoundsHowFarButNotWhichWayStatesNoOrder() {
        String m = """
                module demo

                data Span = Int
                    invariant value >= 0

                data Held = { span: Span }
                data TooFar

                behavior settle : (from: Date, to: Date) -> Held | TooFar
                    constructs Held, Span

                let settle (from, to) = {
                    guard Date.daysBetween(from, to) <= 5 else TooFar
                    Held { span = Span(Date.daysBetween(from, to)) }
                }
                """;
        reads("Span", Verdict.UNKNOWN, m);
    }

    /**
     * And one against something other than nought that does settle the side states the order, which
     * is what the answer running between two ends buys. {@code compare(hi, lo) >= 1} leaves the
     * answer at one, so {@code hi} is above {@code lo} and the difference is above nought.
     *
     * <p>Read as the strict relation and not as the weak one: what it proves here is an invariant
     * that a difference of nought does not satisfy. Read with a zero on the right the same program
     * proves nothing — {@code >= 0} leaves the two equal — which is what tells the two apart.
     */
    @Test
    void aComparisonAgainstSomethingOtherThanZeroThatSettlesTheSide() {
        reads("Above", Verdict.PROVED, aboveZeroUnder("Int.compare(hi, lo) >= 1"));
        reads("Above", Verdict.UNKNOWN, aboveZeroUnder("Int.compare(hi, lo) >= 0"));
    }

    /**
     * A strict end below nought is the weak one at it, over numbers that step. {@code > -1} leaves
     * the answer at nought or one, so the difference is at or above nought and no further — proving
     * an invariant that admits nought and not one that refuses it.
     *
     * <p>Which is the step the numeric domain knows about and this does not say a second time. Said
     * here, a sign would be free to fall between two whole numbers in one reader and not in the
     * other.
     */
    @Test
    void aStrictEndBelowNoughtIsTheWeakOneAtIt() {
        reads("Span", Verdict.PROVED, atOrAboveZeroUnder("Int.compare(hi, lo) > -1"));
        reads("Above", Verdict.UNKNOWN, aboveZeroUnder("Int.compare(hi, lo) > -1"));
    }

    /** A difference held above nought, under the guard {@code written}. */
    private static String aboveZeroUnder(String written) {
        return """
                module demo

                data Above = Int
                    invariant value > 0

                data Held = { span: Above }
                data TooSmall

                behavior settle : (hi: Int, lo: Int) -> Held | TooSmall
                    constructs Held, Above

                let settle (hi, lo) = {
                    guard %s else TooSmall
                    Held { span = Above(hi - lo) }
                }
                """.formatted(written);
    }

    /** The same difference held at or above nought. */
    private static String atOrAboveZeroUnder(String written) {
        return INTS + """

                behavior settle : (hi: Int, lo: Int) -> Held | TooSmall
                    constructs Held, Span

                let settle (hi, lo) = {
                    guard %s else TooSmall
                    Held { span = Span(hi - lo) }
                }
                """.formatted(written);
    }

    /**
     * And past the sign there is nothing to be unsettled about. A comparison answers one of three
     * numbers — which is a bound on its result and not the order it decides ({@code OperationFacts},
     * #1016) — so a guard asking for a second is a guard nothing gets through, and the construction
     * behind it is not reached at all.
     *
     * <p>Beside the test above rather than folded into it: what that one says is that the order is
     * not stated, and it needs a guard something satisfies to say it. This one says where the
     * numbers stop, and needs one nothing does.
     */
    @Test
    void nothingReachesWhatIsBehindAGuardAskingForAFourthSign() {
        String m = INTS + """

                behavior settle : (hi: Int, lo: Int) -> Held | TooSmall
                    constructs Held, Span

                let settle (hi, lo) = {
                    guard Int.compare(hi, lo) >= 2 else TooSmall
                    Held { span = Span(hi - lo) }
                }
                """;
        assertEquals(List.of(), checked("Span", m),
                "a comparison answers at most one, so nothing stands where two was asked for");
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
                    constructs Period

                let span (from, to) = {
                    guard Date.daysBetween(from, to) >= 0 else Backwards
                    Period { from = from, to = to }
                }
                """;
        reads("Period", Verdict.PROVED, m);
    }

    /** The other side of that direction: the same guard says nothing about {@code from} being the
     * later, and a row read the way {@code compare} is read would say it does. */
    @Test
    void aCountForwardSaysNothingOfTheFirstBeingTheGreater() {
        String m = """
                module demo

                data Period = { from: Date, to: Date }
                    invariant notAfter = from >= to

                data Backwards

                behavior span : (from: Date, to: Date) -> Period | Backwards
                    constructs Period

                let span (from, to) = {
                    guard Date.daysBetween(from, to) >= 0 else Backwards
                    Period { from = from, to = to }
                }
                """;
        reads("Period", Verdict.UNKNOWN, m);
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
                    constructs Window

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
                constructs Quote, Rate

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
                    constructs Ordered

                let order (a, b) = {
                    guard a >= b else NotOrdered
                    Ordered { low = b, high = a }
                }
                """;
        reads("Ordered", Verdict.PROVED, m);
    }
}
