package souther.compiler.check;

import souther.compiler.diag.CompileException;
import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.GaveUp;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.InvariantMessage;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A product of two values, and a truncating quotient, are read against what the path knows of what
 * they were computed from.
 *
 * <p>Neither is a linear form, so neither is something the domain can carry: the check names the
 * whole expression an atom, and nothing relates that atom to the factors. What the guards state of
 * the factors is exactly what such a construction needs, and there is no third guard an author could
 * write about the product itself — so left unread, the report asks for something that cannot be
 * written.
 *
 * <p>The rule is not about the operation. Nothing holds of a product wherever it is written; what
 * holds is read off the two factors where the construction stands, which is why this is asked of the
 * domain at the construction rather than stated in a table about {@code *}.
 *
 * <p>Every construction here is written in a behavior, which is where a construction is judged.
 */
class AProductIsBoundedByWhatThePathBoundsItsFactorsToTest {

    private static final String TYPES = """
            module demo
            data NonNeg = Int
                invariant value >= 0
            data NonNegD = Decimal
                invariant value >= 0.0m
            data Pct = Int
                invariant value >= 0 && value <= 100
            data Bad
            """;

    private static List<String> warningsOf(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .map(Diagnostic::code)
                .toList();
    }

    private static Diagnostic errorOf(String module) {
        return assertThrows(CompileException.class,
                () -> Compiler.compileWithWarnings(module)).diagnostic();
    }

    /** The issue's first example: a quantity times a unit price, both guarded at or above zero. */
    @Test
    void aProductOfTwoFactorsGuardedAtOrAboveZeroIsAtOrAboveZero() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior total : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg
                let total (a, b) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0
                        else Bad
                    NonNeg(a * b)
                }
                """));
    }

    /** Two factors a type puts at or above zero need no guard at all: the invariant of an input is
     * what the seeding writes about it. */
    @Test
    void aProductOfTwoValuesTheirTypesBoundIsBounded() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior total : (a: NonNeg, b: NonNeg) -> NonNeg constructs NonNeg
                let total (a, b) = NonNeg(a.value * b.value)
                """));
    }

    /** Given a name first, which is the same value and so the same reading. */
    @Test
    void aProductGivenANameIsBoundedWhereTheProductIs() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior total : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg
                let total (a, b) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0
                        else Bad
                    let product = a * b
                    NonNeg(product)
                }
                """));
    }

    /** Both factors at or below zero is a product at or above zero, which is the corner where two
     * ends nothing bounds meet. */
    @Test
    void aProductOfTwoFactorsAtOrBelowZeroIsAtOrAboveZero() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior total : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg
                let total (a, b) = {
                    guard a <= 0
                        else Bad
                    guard b <= 0
                        else Bad
                    NonNeg(a * b)
                }
                """));
    }

    /** One factor bounded and the other not is a product nothing is known of, and the report stands. */
    @Test
    void aProductWithOneUnboundedFactorIsStillOwed() {
        assertEquals(List.of("E2011"), warningsOf(TYPES + """
                behavior total : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg
                let total (a, b) = {
                    guard a >= 0
                        else Bad
                    NonNeg(a * b)
                }
                """));
    }

    /** A product of two Decimals is exact, so the same reading holds of them. */
    @Test
    void aProductOfTwoDecimalsThePathBoundsIsBounded() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior total : (a: Decimal, b: Decimal) -> NonNegD | Bad constructs NonNegD
                let total (a, b) = {
                    guard a >= 0.0m
                        else Bad
                    guard b >= 0.0m
                        else Bad
                    NonNegD(a * b)
                }
                """));
    }

    /** The issue's second example: a percentage of a guarded value, which is a product the fragment
     * carries under a quotient it does not. */
    @Test
    void aQuotientOfAScaledValueByAWrittenConstantIsBounded() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior part : (x: Int) -> NonNeg | Bad constructs NonNeg
                let part (x) = {
                    guard x >= 0
                        else Bad
                    NonNeg(x * 30 / 100)
                }
                """));
    }

    /** Both ends of the quotient, which is what a clause bounding it above asks for. */
    @Test
    void aQuotientOfAValueBoundedBothWaysIsBoundedBothWays() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior part : (x: Int) -> Pct | Bad constructs Pct
                let part (x) = {
                    guard x >= 0
                        else Bad
                    guard x <= 1000
                        else Bad
                    Pct(x / 10)
                }
                """));
    }

    /** A product under a quotient, so what the quotient lies between follows from what the product
     * was derived to. */
    @Test
    void aQuotientOverAProductReadsWhatTheProductIsBoundedTo() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior part : (a: Int, b: Int) -> Pct | Bad constructs Pct
                let part (a, b) = {
                    guard a >= 0
                        else Bad
                    guard a <= 10
                        else Bad
                    guard b >= 0
                        else Bad
                    guard b <= 1000
                        else Bad
                    Pct(a * b / 100)
                }
                """));
    }

    /**
     * A divisor the path holds away from zero has the sign and the magnitude the rule needs, so the
     * quotient is read off the two ranges as a product is read off its factors.
     *
     * <p>A guard above zero over the whole numbers arrives as an end at one, which is what a strict
     * bound on a discrete atom is sharpened to. What the divisor is <em>written</em> as is not what
     * the rule is about: held as a number it had to be, and a divisor with a coefficient in it went
     * unread however plainly the guards bounded it.
     */
    @Test
    void aQuotientByAValueTheGuardsHoldAwayFromZeroIsBounded() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior part : (x: Int, k: Int) -> NonNeg | Bad constructs NonNeg
                let part (x, k) = {
                    guard x >= 0
                        else Bad
                    guard k > 0
                        else Bad
                    NonNeg(x / k)
                }
                """));
    }

    /**
     * A divisor a type holds away from zero is read the same way: what bounds it is not what the
     * reading asks for.
     *
     * <p>Apportioning a sum by a day count is where this is written, and the invariant that puts the
     * count between one and thirty-one is what keeps the divide off zero. Left unread, the author's
     * way out was to name the quotient and guard it — a refusal in the answer type for a condition
     * that cannot happen, which every caller then has to handle.
     */
    @Test
    void aQuotientByAValueATypeHoldsAwayFromZeroIsBounded() {
        assertEquals(List.of(), warningsOf(TYPES + """
                data Days = Int
                    invariant value >= 1 && value <= 31
                behavior perDay : (total: NonNeg, days: Days) -> NonNeg constructs NonNeg
                let perDay (total, days) = NonNeg(total.value / days.value)
                """));
    }

    /**
     * The end above comes off the divisor's near end, which is a corner a written divisor never
     * had.
     *
     * <p>The witness has an end that nothing but the divide gives: the dividend reaches 100 and the
     * clause stops at 10, so the bound holds only because the divisor is at least 10. A construction
     * whose clause the dividend already satisfies would discharge whatever the divisor was read to.
     */
    @Test
    void theEndAboveAQuotientIsReadOffTheDivisorsNearEnd() {
        assertEquals(List.of(), warningsOf(TYPES + """
                data Party = Int
                    invariant value >= 10 && value <= 31
                data AtMost10 = Int
                    invariant value >= 0 && value <= 10
                behavior each : (bill: Pct, party: Party) -> AtMost10 constructs AtMost10
                let each (bill, party) = AtMost10(bill.value / party.value)
                """));
    }

    /** A product under a quotient by a value, which is the issue's own row: both operands are
     * arithmetic the fragment does not carry, and each is read where it stands. */
    @Test
    void aQuotientOfAProductByAValueReadsBoth() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior part : (a: Int, b: Int, c: Int) -> NonNeg | Bad constructs NonNeg
                let part (a, b, c) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0
                        else Bad
                    guard c > 0
                        else Bad
                    NonNeg(a * b / c)
                }
                """));
    }

    /**
     * A divisor nothing holds away from zero is one this rule says nothing about, and the clause
     * stands.
     *
     * <p>Holding every admitted divisor off zero is what the rule asks for before it states
     * anything, and what is written here does not. That is not a claim that the divides which do
     * answer are unbounded — over the whole numbers this one divides by at least one — it is that a
     * rule stated over the ends of a range is not one that can answer for a range through zero.
     */
    @Test
    void aQuotientByAValueNothingHoldsAwayFromZeroIsStillOwed() {
        assertEquals(List.of("E2011"), warningsOf(TYPES + """
                behavior part : (x: Int, k: Int) -> NonNeg | Bad constructs NonNeg
                let part (x, k) = {
                    guard x >= 0
                        else Bad
                    guard k >= 0
                        else Bad
                    NonNeg(x / k)
                }
                """));
    }

    /**
     * A divisor the path holds below zero puts the quotient on the other side, and a construction
     * the value fails is refused.
     *
     * <p>The end that decides it is the one the divisor's <em>near</em> end gives: the greatest the
     * quotient gets is the dividend's least over the divisor's furthest, which is {@code -10} here
     * and not the {@code -100} the two written ends taken in order would pair.
     */
    @Test
    void aQuotientByAValueHeldBelowZeroIsRefused() {
        assertEquals("E2010", errorOf(TYPES + """
                data SmallNeg = Int
                    invariant value >= 0 - 10 && value <= 0 - 1
                behavior part : (x: Int, k: SmallNeg) -> NonNeg | Bad constructs NonNeg
                let part (x, k) = {
                    guard x >= 100
                        else Bad
                    NonNeg(x / k.value)
                }
                """).code());
    }

    /**
     * A divisor that is a number no {@code Int} holds is not one the rule reads, and the clause is
     * owed as it is owed over any other value nothing is known of.
     *
     * <p>The arithmetic a form is composed of runs over numbers of any size, and the operator's
     * divisor is a value of its own type — so what the reading proves of this one is a range with no
     * {@code Int} anywhere in it. That is not a divisor this operator has, and a rule with no operand
     * to fire on contributes nothing. It is <em>not</em> read as a range holding no value: taken into
     * the domain that would be a contradiction, and a contradictory domain proves every clause there
     * is, so the construction would come out discharged rather than owed.
     *
     * <p>Asked of what the analysis did and not only of what it did not say. This check is fail-open
     * — a walk that falls over reports exactly what a walk that finished and found nothing reports
     * ({@link InvariantChecker#GAVE_UP}) — so a warning count alone would pass just as well on an
     * analysis that stopped at this divisor, which is how the number no {@code Int} holds was
     * declined before there was a rule about it.
     */
    @Test
    void aDivisorNoIntCanHoldIsNotOneTheRuleReads() {
        List<Said> said = new ArrayList<>();
        List<GaveUp> gaveUp = new ArrayList<>();
        InvariantChecker.WATCHING = said;
        InvariantChecker.GAVE_UP = gaveUp;
        try {
            assertEquals(List.of("E2011"), warningsOf(TYPES + """
                    behavior part : (x: Int) -> NonNeg | Bad constructs NonNeg
                    let part (x) = {
                        guard x >= 0
                            else Bad
                        NonNeg(x / (9223372036854775807 + 1))
                    }
                    """));
        } finally {
            InvariantChecker.WATCHING = null;
            InvariantChecker.GAVE_UP = null;
        }

        assertEquals(List.of(), gaveUp, "the analysis ran to the end");
        assertEquals(List.of(Verdict.UNKNOWN),
                said.stream().map(Said::verdict).toList(),
                "the construction was reached and the clause came out unproven");
    }

    /**
     * {@code /} on {@code Decimal} rounds rather than truncating, and where an end lands under that
     * rounding is not something this states — so the quotient is read as nothing and the clause
     * stands.
     *
     * <p>The witness has an end. Read as a truncating divide, {@code x / 100.0m} for an {@code x}
     * between zero and one would come out at zero and discharge a clause the values fail —
     * {@code 0.01m} is above zero. A witness bounded below only would come out right by accident,
     * and would say nothing about whether the rounding was read.
     */
    @Test
    void aDecimalQuotientIsNotRead() {
        assertEquals(List.of("E2011"), warningsOf(TYPES + """
                data NotAbove = Decimal
                    invariant value <= 0.0m
                behavior part : (x: Decimal) -> NotAbove | Bad constructs NotAbove
                let part (x) = {
                    guard x >= 0.0m
                        else Bad
                    guard x <= 1.0m
                        else Bad
                    NotAbove(x / 100.0m)
                }
                """));
    }

    /**
     * A clause naming a value a guard equated with a product is discharged through that guard,
     * though the clause names no product at all.
     *
     * <p>What is derived about the product reaches {@code total} through the domain's own relation
     * between the two, which is what makes the derivations a reading of the whole domain rather
     * than of the clause. Left to the atoms a clause names, this construction is owed a guard that
     * is already written — so what this holds is not today's answer alone but what a narrower
     * reading would have to keep answering.
     */
    @Test
    void aClauseReachesAProductThroughAGuardThatEquatesTheTwo() {
        assertEquals(List.of(), warningsOf(TYPES + """
                behavior total : (a: Int, b: Int, total: Int) -> NonNeg | Bad
                    constructs NonNeg
                let total (a, b, total) = {
                    guard a >= 0
                        else Bad
                    guard b >= 0
                        else Bad
                    guard total == a * b
                        else Bad
                    NonNeg(total)
                }
                """));
    }

    /**
     * A factor that can be zero is a product that can be zero, and a clause the zero satisfies is
     * not one the product fails.
     *
     * <p>{@code a} is at or above zero and {@code b} is above it without reaching it, so the
     * product is at or above zero and reaches it — at {@code a = 0}, whatever {@code b} is. A
     * reading that took the ends of the two factors together would have the product strictly above
     * zero and would report the construction as one the value fails, which is untrue of the value
     * built where {@code a} is zero.
     */
    @Test
    void aProductWithAFactorThatCanBeZeroIsNotRefusedForBeingAboveZero() {
        assertEquals(List.of("E2011"), warningsOf(TYPES + """
                data NotAbove = Decimal
                    invariant value <= 0.0m
                behavior total : (a: Decimal, b: Decimal) -> NotAbove | Bad constructs NotAbove
                let total (a, b) = {
                    guard a >= 0.0m
                        else Bad
                    guard a <= 1.0m
                        else Bad
                    guard b > 0.0m
                        else Bad
                    guard b < 1.0m
                        else Bad
                    NotAbove(a * b)
                }
                """));
    }

    /**
     * A factor the guards pin to zero is a product that is zero, and what is derived of it is a
     * range holding that one value.
     *
     * <p>A range holding nothing would be a contradiction to the domain it is taken into, and a
     * domain holding one proves every clause — so the construction would come out discharged
     * however far its invariant is from what the value is. The witness asks for a clause the value
     * plainly fails, and gets the error rather than silence.
     */
    @Test
    void aProductPinnedToZeroIsReadAsZeroAndNotAsNoValueAtAll() {
        assertEquals("E2010", errorOf(TYPES + """
                data FarBelow = Decimal
                    invariant value <= 0.0m - 1000.0m
                behavior total : (a: Decimal, b: Decimal) -> FarBelow | Bad constructs FarBelow
                let total (a, b) = {
                    guard a >= 0.0m
                        else Bad
                    guard a <= 0.0m
                        else Bad
                    guard b > 1.0m
                        else Bad
                    guard b < 2.0m
                        else Bad
                    FarBelow(a * b)
                }
                """).code());
    }

    /**
     * A product refused by what the factors' own types say is refused wherever it is built, and the
     * error says so: nothing about the path is what rejects it.
     *
     * <p>The two readings of a construction — under what the guards established, and under what
     * holds of the values whatever the guards did — are each given what follows about the
     * arithmetic in them. Derived into the first alone, this would be a value rejected "on a
     * reachable path", which tells an author to guard a path that is not what is wrong.
     */
    @Test
    void aProductRefusedByTheFactorsOwnTypesIsRefusedWhereverItIsBuilt() {
        Diagnostic said = errorOf(TYPES + """
                data Negative = Int
                    invariant belowZero = value <= 0 - 1
                behavior total : (a: NonNeg, b: NonNeg) -> Negative constructs Negative
                let total (a, b) = Negative(a.value * b.value)
                """);

        assertInstanceOf(InvariantMessage.TheValueIsOneTheInvariantRejects.class, said.said(),
                "the types refuse it, so no path is what does: " + said.said());
    }

    /**
     * A product the guards put on the other side of zero is a construction the value fails, which is
     * an error and not a warning: a derived bound refutes a clause as readily as it discharges one.
     */
    @Test
    void aProductThePathPutsBelowZeroIsRefused() {
        assertEquals("E2010", errorOf(TYPES + """
                behavior total : (a: Int, b: Int) -> NonNeg | Bad constructs NonNeg
                let total (a, b) = {
                    guard a >= 1
                        else Bad
                    guard b <= 0 - 1
                        else Bad
                    NonNeg(a * b)
                }
                """).code());
    }
}
