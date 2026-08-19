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
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value reached through a call this analysis expands is the value the call's body reads, so a
 * construction over it is checked as the construction over that value is.
 *
 * <p>An expansion binds each argument and reads the parameter through that binding. Where the
 * binding stands inside a value — under a field read, under one side of a comparison — it is not one
 * the walk steps into, so what it holds is a name nothing entered, the chain off it names no
 * location, and a construction over a term nothing can name is owed no clause at all. That is a
 * construction leaving the check, and it reads in the source exactly as a discharge does.
 *
 * <p>Which is why these are read off the verdicts. A construction the check dropped and one its
 * guards established are the same absence in the output, so a test that reads the diagnostics can be
 * satisfied by the defect it is meant to hold: {@link Verdict#UNREPRESENTABLE} is the silence this
 * file is about and {@link Verdict#PROVED} is the one it wants. The unguarded cases are held to
 * their diagnostic as well, since what an author acts on is what is reported.
 */
class AValueReachedThroughACallIsTheValueItStandsForTest {

    /**
     * A model whose helpers name a place. {@code Net} is what the construction under test builds, so
     * that what is asserted of it is not confused with the constructions inside a helper.
     */
    private static final String LOCATES = """
            module demo

            data Amount = Decimal
                invariant value >= 0.0m

            data Net = Decimal
                invariant value >= 0.0m

            data Order = { amount: Amount }
            data Line = { order: Order }
            data Refund = { net: Net }
            data FeeTooHigh

            let amountOf (order: Order): Amount = order.amount
            let orderOf (line: Line): Order = line.order
            """;

    /** The same model with helpers whose bodies compute a value rather than name a place. */
    private static final String COMPUTES = """
            module demo

            data Amount = Decimal
                invariant value >= 0.0m

            data Net = Decimal
                invariant value >= 0.0m

            data Earnings = { fixed: Amount, uplift: Amount }
            data Deductions = { tax: Amount, premium: Amount }
            data Refund = { net: Net }
            data FeeTooHigh

            let grossOf (e: Earnings): Amount = e.fixed + e.uplift
            let deductionTotal (d: Deductions): Amount = d.tax + d.premium

            behavior settle : (e: Earnings, d: Deductions) -> Refund | FeeTooHigh
                constructs Refund, Net
            """;

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

    /** Every verdict reached on a construction of {@code type}, which is at least one: a type nothing
     * was said of is a construction the check never reached, and that is the defect here. */
    private static List<Verdict> verdictsOn(String type, String source) {
        List<Verdict> on = verdictsIn(source).stream()
                .filter(s -> s.type().equals(type)).map(Said::verdict).toList();
        assertFalse(on.isEmpty(), "no construction of `" + type + "` was checked at all");
        return on;
    }

    private static void reads(String type, Verdict expected, String source) {
        for (Verdict verdict : verdictsOn(type, source)) {
            assertEquals(expected, verdict, "on a construction of `" + type + "`");
        }
    }

    private static boolean warns(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    // --- what the call stands for ---------------------------------------------------------------

    /** The construction the report is about: nothing is guarded and `fee` may exceed what the order
     * holds, so the subtraction can be negative and this is a possible abort. */
    @Test
    void aFieldReadOnACallIsTheChainItStandsFor() {
        String m = LOCATES + """

                behavior settle : (order: Order, fee: Amount) -> Refund
                    constructs Refund, Net

                let settle (order, fee) = {
                    Refund { net = Net(amountOf(order).value - fee.value) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
        assertTrue(warns(m), "and an author is told: this is what E2011 is for");
    }

    /** The same construction written as the chain the call stands for. */
    @Test
    void theChainItStandsForIsTheSameConstruction() {
        String m = LOCATES + """

                behavior settle : (order: Order, fee: Amount) -> Refund
                    constructs Refund, Net

                let settle (order, fee) = {
                    Refund { net = Net(order.amount.value - fee.value) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
    }

    /** More than one field between the call and the number. */
    @Test
    void aFieldReadOfMoreThanOneLevelOnACall() {
        String m = LOCATES + """

                behavior settle : (line: Line, fee: Amount) -> Refund
                    constructs Refund, Net

                let settle (line, fee) = {
                    Refund { net = Net(orderOf(line).amount.value - fee.value) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
    }

    /** The place a field is read off is itself a call's binding. */
    @Test
    void aFieldReadOnACallGivenACall() {
        String m = LOCATES + """

                behavior settle : (line: Line, fee: Amount) -> Refund
                    constructs Refund, Net

                let settle (line, fee) = {
                    Refund { net = Net(amountOf(orderOf(line)).value - fee.value) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
    }

    /** One operand of two reads through a call, and an expression is not readable in one operand and
     * unreadable in the other. */
    @Test
    void oneOperandReadThroughACall() {
        String m = LOCATES + """

                behavior settle : (order: Order, fee: Amount) -> Refund
                    constructs Refund, Net

                let settle (order, fee) = {
                    Refund { net = Net(fee.value - amountOf(order).value) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
    }

    /** Read through the call the two operands are one location, and a location less itself is zero —
     * proved, rather than an unknown nothing was said about. */
    @Test
    void aDifferenceOfOneLocationSpelledTwoWaysIsZero() {
        String m = LOCATES + """

                behavior settle : (order: Order) -> Refund
                    constructs Refund, Net

                let settle (order) = {
                    Refund { net = Net(order.amount.value - amountOf(order).value) }
                }
                """;
        reads("Net", Verdict.PROVED, m);
    }

    /** A guard over the same call establishes the construction. */
    @Test
    void aGuardOverTheSameCallEstablishesTheConstruction() {
        String m = LOCATES + """

                behavior settle : (order: Order, fee: Amount) -> Refund | FeeTooHigh
                    constructs Refund, Net

                let settle (order, fee) = {
                    guard amountOf(order).value >= fee.value else FeeTooHigh
                    Refund { net = Net(amountOf(order).value - fee.value) }
                }
                """;
        reads("Net", Verdict.PROVED, m);
        assertFalse(warns(m), "and nothing is reported of a construction the guard settled");
    }

    /** And no more than it establishes. */
    @Test
    void theGuardOverACallEstablishesNoMoreThanItSays() {
        String m = LOCATES + """

                behavior settle : (order: Order, fee: Amount) -> Refund | FeeTooHigh
                    constructs Refund, Net

                let settle (order, fee) = {
                    guard amountOf(order).value >= fee.value else FeeTooHigh
                    Refund { net = Net(amountOf(order).value - fee.value - 1.0m) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
    }

    /** Binding the call's result to a name first is the spelling that already worked, and is what
     * the ones above are held to. */
    @Test
    void theCallBoundToANameFirst() {
        String m = LOCATES + """

                behavior settle : (order: Order, fee: Amount) -> Refund
                    constructs Refund, Net

                let settle (order, fee) = {
                    let paid = amountOf(order)
                    Refund { net = Net(paid.value - fee.value) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
    }

    // --- a helper that computes rather than locates ----------------------------------------------

    /**
     * The shape every "take the deductions off the gross" behavior has. Neither operand is a place,
     * so what makes the guard and the construction meet is that both are read through the expansion:
     * the guard states the difference over the fields the two bodies read, and the construction takes
     * the same two.
     */
    @Test
    void aGuardOverWhatTwoCallsComputeEstablishesTheirDifference() {
        String m = COMPUTES + """

                let settle (e, d) = {
                    guard grossOf(e) >= deductionTotal(d) else FeeTooHigh
                    Refund { net = Net(grossOf(e).value - deductionTotal(d).value) }
                }
                """;
        reads("Net", Verdict.PROVED, m);
    }

    /** And one step past what that guard settles is an unknown. */
    @Test
    void aGuardOverWhatTwoCallsComputeEstablishesNoMore() {
        String m = COMPUTES + """

                let settle (e, d) = {
                    guard grossOf(e) >= deductionTotal(d) else FeeTooHigh
                    Refund { net = Net(grossOf(e).value - deductionTotal(d).value - 1.0m) }
                }
                """;
        reads("Net", Verdict.UNKNOWN, m);
        assertTrue(warns(m), "and an author is told");
    }

    // --- where the binding stands --------------------------------------------------------------

    /**
     * A binding is entered where it stands, and where it stands is inside whatever chose to evaluate
     * it. A branch is read with its condition assumed, so an expansion written in one is read there
     * and not at the conditional — lifted out, its construction would be read where the condition
     * that establishes it does not hold.
     */
    @Test
    void anExpansionInABranchIsReadUnderTheConditionThatChoseIt() {
        String m = """
                module demo

                data Net = Decimal
                    invariant value >= 0.0m

                data Refund = { net: Net }

                let same (n: Net): Net = n

                behavior settle : (x: Decimal) -> Refund
                    constructs Refund, Net

                let settle (x) = Refund { net = if x >= 0.0m then same(Net(x)) else Net(0.0m) }
                """;
        reads("Net", Verdict.PROVED, m);
        assertFalse(warns(m), "the branch that builds from `x` is the one `x >= 0.0m` chose");
    }

    /** The same of what a `match` arm binds: an expansion reading it is read inside the arm, where
     * the binding carries what the case guarantees. */
    @Test
    void anExpansionInAnArmIsReadUnderWhatTheArmBinds() {
        String m = """
                module demo

                data Span = Int
                    invariant value >= 0

                data Small = { lo: Int, hi: Int }
                    invariant lo <= hi
                data Large = { lo: Int, hi: Int }
                    invariant lo <= hi
                data Kind = Small | Large

                let same (n: Int): Int = n

                behavior widthOf : (k: Kind) -> Span
                    constructs Span

                let widthOf (k) = match k with
                    | Small as s -> Span(same(s.hi) - s.lo)
                    | Large as l -> Span(same(l.hi) - l.lo)
                """;
        reads("Span", Verdict.PROVED, m);
        assertFalse(warns(m), "what the arm binds carries `lo <= hi`, which is the difference");
    }

    /** And of what an attempted construction binds: the success branch holds what the attempt built,
     * so an expansion reading it is read there. */
    @Test
    void anExpansionInASuccessBranchIsReadUnderWhatTheAttemptBuilt() {
        String m = """
                module demo

                data Net = Decimal
                    invariant value >= 0.0m
                data Half = Decimal
                    invariant value >= 0.0m
                data NotANet

                let same (n: Net): Net = n

                behavior halve : (x: Decimal) -> Half | NotANet
                    constructs Half, Net

                let halve (x) = {
                    if Net(x) as n then Half(same(n).value) else NotANet
                }
                """;
        reads("Half", Verdict.PROVED, m);
        assertFalse(warns(m), "`n` is what the attempt built, and it holds `Net`'s invariant");
    }
}
