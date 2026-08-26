package souther.compiler;

import java.util.List;
import java.util.Locale;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Messages;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What every case of a sum spreads holds of a value of the sum, so a construction reached through
 * one is established by it.
 *
 * <p>The same value, reached the same way, has to be established in both shapes. A model holding its
 * amounts in a record and a model holding them in a sum of categories differ by the sum between the
 * line and its amount, and that is not a difference the rules know about: every amount summed is an
 * amount, so every one of them satisfies what an amount states, and so does their total.
 *
 * <p>Which is a claim about the sharing being nominal and not about sums in general. The last test
 * is the other side of it: cases that merely declare a field of the same name share nothing, and a
 * construction reached through one of those is established by nothing.
 */
class WhatEveryCaseOfASumSpreadsEstablishesAConstructionTest {

    private static List<String> warningsOf(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .map(Diagnostic::code)
                .toList();
    }

    private static String said(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .map(d -> Messages.render(d.said(), Locale.ENGLISH))
                .findFirst()
                .orElse("");
    }

    /** A field every case spreads is read off the sum, and what its type states comes with it. */
    @Test
    void anAmountBehindASumIsStillAnAmount() {
        assertEquals(List.of(), warningsOf("""
                module demo

                data Amount = Int
                    invariant value >= 0

                data Costed = { amount: Amount }
                data Travel = { ...Costed }
                data Lodging = { ...Costed }
                data Expense = Travel | Lodging

                data Line = { expense: Expense }

                let total (lines: List<Line>): Int =
                    List.sum(List.map(one -> one.expense.amount.value, lines))

                behavior totalled : (lines: List<Line>) -> Amount
                    constructs Amount
                let totalled (lines) = Amount(total(lines))
                """));
    }

    /** And so is one held directly by the elements of a container. */
    @Test
    void anAmountBehindASumHeldByAContainerIsStillAnAmount() {
        assertEquals(List.of(), warningsOf("""
                module demo

                data Amount = Int
                    invariant value >= 0

                data Costed = { amount: Amount }
                data Travel = { ...Costed }
                data Lodging = { ...Costed }
                data Expense = Travel | Lodging

                let total (expenses: List<Expense>): Int =
                    List.sum(List.map(one -> one.amount.value, expenses))

                behavior totalled : (expenses: List<Expense>) -> Amount
                    constructs Amount
                let totalled (expenses) = Amount(total(expenses))
                """));
    }

    /** A relation the shared declaration states holds of every case, so a spread of the sum carries
     *  it to what is built out of it. */
    @Test
    void aRelationEveryCaseSpreadsCarriesThroughASpreadOfTheSum() {
        assertEquals(List.of(), warningsOf("""
                module demo

                data Period =
                    { from: Date
                    , to: Date
                    }
                    invariant Date.daysBetween(from, to) >= 0

                data Draft = { ...Period }
                data Sealed = { ...Period, at: Date }
                data Filed = Draft | Sealed

                data Reopened = { ...Period }

                behavior reopen : (filed: Filed) -> Reopened
                    constructs Reopened

                let reopen (filed) = Reopened { ...filed }
                """));
    }

    /**
     * Cases that share no spread state nothing of a value of the sum.
     *
     * <p>Sharing is nominal: two cases holding a field of one name have not shared it, so nothing
     * here is established and the construction is still one an author has to answer for.
     */
    @Test
    void casesThatShareNoSpreadEstablishNothing() {
        String source = """
                module demo

                data Amount = Int
                    invariant value >= 0

                data Travel = { fare: Amount }
                data Lodging = { rate: Amount }
                data Expense = Travel | Lodging

                behavior totalled : (expense: Expense, n: Int) -> Amount
                    constructs Amount
                let totalled (expense, n) = Amount(n)
                """;

        assertEquals(List.of("E2011"), warningsOf(source));
        assertFalse(said(source).isEmpty(), "and it says which construction it is about");
    }
}
