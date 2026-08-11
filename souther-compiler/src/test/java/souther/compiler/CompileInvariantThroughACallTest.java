package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value reached through a call the analysis expands is the value the call's body reads, so a
 * construction over it is checked as the construction over that value is.
 *
 * <p>The check reads the module's own helpers expanded, which binds each argument and reads the
 * parameter through that binding. Where such a call stands as the target of a field read, what the
 * field is read from is a binding rather than a name the body wrote, and a term the check could not
 * name is one no clause is owed against: the construction leaves the check, and E2011 is silent for
 * a construction that violates on every input.
 *
 * <p>So these are written without a guard wherever they can be. A construction nothing establishes
 * is one the diagnostic must be raised for whatever the discharge machinery can prove, which is what
 * tells a silence that discharged from a silence that dropped the construction — the two are the
 * same absence in the output, and the second is what this file is about.
 */
class CompileInvariantThroughACallTest {

    private static final String DECLS = """
            module demo

            data Amount = Decimal
                invariant value >= 0.0m

            data Order = { amount: Amount }
            data Line = { order: Order }
            data Refund = { amount: Amount }
            data FeeTooHigh

            let amountOf (order: Order): Amount = order.amount
            let orderOf (line: Line): Order = line.order
            """;

    /** The same model with helpers whose bodies compute a value rather than name a place. */
    private static final String COMPUTED = """
            module demo

            data Amount = Decimal
                invariant value >= 0.0m

            data Earnings = { fixed: Amount, uplift: Amount }
            data Deductions = { tax: Amount, premium: Amount }
            data Slip = { net: Amount }
            data FeeTooHigh

            let grossOf (e: Earnings): Amount = e.fixed + e.uplift
            let deductionTotal (d: Deductions): Amount = d.tax + d.premium

            behavior settle : (e: Earnings, d: Deductions) -> Slip | FeeTooHigh
                constructs Slip, Amount, FeeTooHigh
            """;

    private static boolean hasWarning(Compiler.Compiled c, String code) {
        return c.warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && code.equals(d.code()));
    }

    /** The construction the whole report is about: nothing is guarded, and `fee` may exceed what the
     * order holds, so the subtraction can be negative and E2011 stands between it and an abort. */
    @Test
    void aFieldReadOnACallIsCheckedAsTheChainItStandsFor() {
        String m = DECLS + """

                behavior settle : (order: Order, fee: Amount) -> Refund
                    constructs Refund, Amount

                let settle (order, fee) = {
                    Refund { amount = Amount(amountOf(order).value - fee.value) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "an unguarded subtraction is E2011 whether the term is written as a field chain or"
                        + " read through a call the analysis expands");
    }

    /** The same construction written as the chain the call stands for. Its diagnostic is what the
     * one above is held to; without it a fix could be read off a single spelling. */
    @Test
    void theChainItStandsForIsTheSameConstruction() {
        String m = DECLS + """

                behavior settle : (order: Order, fee: Amount) -> Refund
                    constructs Refund, Amount

                let settle (order, fee) = {
                    Refund { amount = Amount(order.amount.value - fee.value) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the field chain is the construction the call spelling is compared against");
    }

    /** More than one field between the call and the number. */
    @Test
    void aFieldReadOfMoreThanOneLevelOnACall() {
        String m = DECLS + """

                behavior settle : (line: Line, fee: Amount) -> Refund
                    constructs Refund, Amount

                let settle (line, fee) = {
                    Refund { amount = Amount(orderOf(line).amount.value - fee.value) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the number is reached by two fields off the call, and is still the location it is");
    }

    /** One operand of the shape is enough to drop a construction: what cannot be read is read as
     * nothing, and nothing is what the whole expression then is. */
    @Test
    void oneOperandReadThroughACall() {
        String m = DECLS + """

                behavior settle : (order: Order, fee: Amount) -> Refund
                    constructs Refund, Amount

                let settle (order, fee) = {
                    Refund { amount = Amount(fee.value - amountOf(order).value) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "an expression is not readable in one operand and unreadable in the other");
    }

    /** The other side of the same coin: read through the call, the two operands are one location,
     * and their difference is zero rather than a number nothing is known about. A construction the
     * check drops and one it discharges are the same silence, so this is held beside a spelling
     * whose silence would be wrong. */
    @Test
    void aDifferenceOfOneLocationSpelledTwoWaysIsZero() {
        String m = DECLS + """

                behavior settle : (order: Order) -> Refund
                    constructs Refund, Amount

                let settle (order) = {
                    Refund { amount = Amount(order.amount.value - amountOf(order).value) }
                }
                """;
        assertFalse(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "`amountOf(order).value` is `order.amount.value`, and a location less itself is zero");
    }

    /** A call given a call: the binding under the field read holds another expansion, and what it
     * denotes is read through that one. */
    @Test
    void aFieldReadOnACallGivenACall() {
        String m = DECLS + """

                behavior settle : (line: Line, fee: Amount) -> Refund
                    constructs Refund, Amount

                let settle (line, fee) = {
                    Refund { amount = Amount(amountOf(orderOf(line)).value - fee.value) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the place a field is read off is a binding whose own value is one");
    }

    /** With no arithmetic at all: the field read is the whole of what is dropped. */
    @Test
    void aFieldReadOnACallAgainstAConstant() {
        String m = DECLS + """

                behavior settle : (order: Order) -> Refund
                    constructs Refund, Amount

                let settle (order) = {
                    Refund { amount = Amount(amountOf(order).value - 100.0m) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the arithmetic is not what makes the term unreadable");
    }

    /**
     * The other half: a guard over the same call establishes the construction, and the check says
     * nothing. Read on its own this is satisfied by dropping the construction, which is what happens
     * today — it holds together with the unguarded cases above, and only together with them.
     */
    @Test
    void aGuardOverTheSameCallEstablishesTheConstruction() {
        String m = DECLS + """

                behavior settle : (order: Order, fee: Amount) -> Refund | FeeTooHigh
                    constructs Refund, Amount, FeeTooHigh

                let settle (order, fee) = {
                    guard amountOf(order).value >= fee.value else FeeTooHigh
                    Refund { amount = Amount(amountOf(order).value - fee.value) }
                }
                """;
        assertFalse(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the guard states the relation the construction needs, read through the same call");
    }

    /** And the guard establishes what it says and no more: one step past what it settles is a
     * warning, which is what tells the silence above from a construction nothing looked at. */
    @Test
    void theGuardOverACallEstablishesNoMoreThanItSays() {
        String m = DECLS + """

                behavior settle : (order: Order, fee: Amount) -> Refund | FeeTooHigh
                    constructs Refund, Amount, FeeTooHigh

                let settle (order, fee) = {
                    guard amountOf(order).value >= fee.value else FeeTooHigh
                    Refund { amount = Amount(amountOf(order).value - fee.value - 1.0m) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "one step past the guard is not established, and the check is reading the term");
    }

    /**
     * A helper whose body computes rather than locates: what the call answers is arithmetic over the
     * caller's terms, and a guard over two such calls establishes the difference between them.
     *
     * <p>The shape every "take the deductions off the gross" behavior has. Neither operand is a
     * place, so what makes the guard and the construction meet is that both are read through the
     * expansion — the guard states `gross - deductions >= 0` over the fields the two bodies read,
     * and the construction subtracts the same two.
     */
    @Test
    void aGuardOverWhatTwoCallsComputeEstablishesTheirDifference() {
        String m = COMPUTED + """

                let settle (e, d) = {
                    guard grossOf(e) >= deductionTotal(d) else FeeTooHigh
                    Slip { net = Amount(grossOf(e).value - deductionTotal(d).value) }
                }
                """;
        assertFalse(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the guard states the difference the construction takes");
    }

    /** And one step past what that guard settles is a warning: the terms are being read, not
     * dropped. */
    @Test
    void aGuardOverWhatTwoCallsComputeEstablishesNoMore() {
        String m = COMPUTED + """

                let settle (e, d) = {
                    guard grossOf(e) >= deductionTotal(d) else FeeTooHigh
                    Slip { net = Amount(grossOf(e).value - deductionTotal(d).value - 1.0m) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "one step past the guard is not established, and the check is reading the terms");
    }

    /** Binding the call's result to a name first is the spelling that works today, and is what the
     * spellings above are held to. */
    @Test
    void theCallBoundToANameFirst() {
        String m = DECLS + """

                behavior settle : (order: Order, fee: Amount) -> Refund
                    constructs Refund, Amount

                let settle (order, fee) = {
                    let paid = amountOf(order)
                    Refund { amount = Amount(paid.value - fee.value) }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a name bound to the call's result reads the field off a location");
    }
}
