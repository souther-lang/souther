package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two totals of one list, each adding one number of the elements standing at a case of a field,
 * held equal, are a rule of the list as a whole and are read at it.
 *
 * <p>{@code sideTotal(Debit, postings) == sideTotal(Credit, postings)}, the totals being walks of
 * the postings that add an amount where the side is the one asked for. A total is a number made by
 * a walk and not a position, so the rule was read as one about a derived value and left a question
 * standing at the list.
 */
class ATotalOfOneCaseHeldEqualToTheTotalOfAnotherIsReadTest {

    private static String journal(String balanced, String side) {
        return """
                module demo

                import List ( fold, length )

                data Amount = Decimal
                    invariant value >= 0.0m
                data Side = Debit | Credit
                data Posting = { side: Side, amount: Amount, memo: String }

                let sideTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.%s) else acc,
                         0.0m, postings)

                data N = { postings: List<Posting> }
                    invariant twoSided = length(postings) >= 2
                    invariant balanced = %s

                behavior probe : (n: N) -> Int
                let probe (n) = 1
                """.formatted(side, balanced);
    }

    private static final String EQUAL =
            "Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 0";

    @Test
    void theListOfBalancedSidesIsAnswered() {
        assertEquals(List.of(), unansweredAtTheList(journal(EQUAL, "amount.value")));
    }

    @Test
    void theTotalsWrittenTheOtherWayRoundAreTheSameRule() {
        assertEquals(List.of(), unansweredAtTheList(journal(
                "Decimal.compare(sideTotal(Credit, postings), sideTotal(Debit, postings)) == 0",
                "amount.value")));
    }

    @Test
    void totalsThatAreOnlyOrderedStayUnanswered() {
        assertFalse(unansweredAtTheList(journal(
                "Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) >= 0",
                "amount.value")).isEmpty());
    }

    @Test
    void aTotalHeldToNoOtherTotalStaysUnanswered() {
        assertFalse(unansweredAtTheList(journal(
                "Decimal.compare(sideTotal(Debit, postings), 0.0m) == 0", "amount.value"))
                .isEmpty());
    }

    /**
     * Two pairs of sides held equal over one list are two equations over the same elements, and the
     * builders solve one: the second is a rule they are never told, so it is not called read.
     */
    @Test
    void twoPairsOfSidesOverOneListStayUnanswered() {
        assertFalse(unansweredAtTheList("""
                module demo

                import List ( fold, length )

                data Amount = Decimal
                    invariant value >= 0.0m
                data Side = Debit | Credit
                data Posting = { side: Side, amount: Amount, fee: Amount }

                let amounts (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.amount.value) else acc,
                         0.0m, postings)

                let fees (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.fee.value) else acc,
                         0.0m, postings)

                data N = { postings: List<Posting> }
                    invariant amountsBalance =
                        Decimal.compare(amounts(Debit, postings), amounts(Credit, postings)) == 0
                    invariant feesBalance =
                        Decimal.compare(fees(Debit, postings), fees(Credit, postings)) == 0

                behavior probe : (n: N) -> Int
                let probe (n) = 1
                """).isEmpty());
    }

    /**
     * An element with a rule of its own is one whose amounts depend on its other fields, and
     * amounts chosen among those the amount type admits are not chosen against that rule: a debit
     * of one beside a credit of one is a list the rule refuses, and a debit of ten beside a credit
     * of ten is one it allows. The rule is not read as kept, and stays unanswered.
     */
    @Test
    void anElementWithARuleOfItsOwnLeavesTheBalanceUnanswered() {
        assertFalse(unansweredAtTheList("""
                module demo

                import List ( fold, length )

                data Amount = Decimal
                    invariant value >= 1.0m
                data Side = Debit | Credit
                data Posting = { side: Side, amount: Amount }
                    invariant side == Credit || amount.value >= 10.0m

                let sideTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.amount.value) else acc,
                         0.0m, postings)

                data N = { postings: List<Posting> }
                    invariant balanced =
                        Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 0

                behavior probe : (n: N) -> Int
                let probe (n) = 1
                """).isEmpty());
    }

    /**
     * A rule of the element that could not be read is still a rule it has: nothing read of it is
     * not the same as nothing written, and an element is taken for one with no rule only where
     * none is declared. A rule that stops the reading leaves no statement at all, so the list of
     * statements is empty beside it.
     */
    @Test
    void anElementWhoseRuleCouldNotBeReadIsNotTakenForOneWithNone() {
        assertFalse(unansweredAtTheList("""
                module demo

                import List ( fold, length )

                data Amount = Decimal
                    invariant value >= 1.0m
                data Side = Debit | Credit
                data Posting = { side: Side, amount: Amount }
                    invariant unreadable = loop(amount.value)

                let loop (d: Decimal): Bool = loop(d)

                let sideTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.amount.value) else acc,
                         0.0m, postings)

                data N = { postings: List<Posting> }
                    invariant balanced =
                        Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 0

                behavior probe : (n: N) -> Int
                let probe (n) = 1
                """).isEmpty());
    }

    /**
     * A rule of the record itself that could not be read may keep the elements apart, bound how
     * many it holds or relate the list to another field, and nothing is built for the balance
     * beside it: not found among the rules read is not absent from the rules.
     */
    @Test
    void aRecordWithARuleNoReadingTookInLeavesTheBalanceUnanswered() {
        assertFalse(unansweredAtTheList("""
                module demo

                import List ( fold, length )

                data Amount = Decimal
                    invariant value >= 0.0m
                data Side = Debit | Credit
                data Posting = { side: Side, amount: Amount }

                let loop (d: Decimal): Bool = loop(d)

                let sideTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.amount.value) else acc,
                         0.0m, postings)

                data N = { postings: List<Posting> }
                    invariant balanced =
                        Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 0
                    invariant unreadable = loop(0.0m)

                behavior probe : (n: N) -> Int
                let probe (n) = 1
                """).isEmpty());
    }

    /** What stands unanswered at the list of the input of {@code probe}. */
    private static List<String> unansweredAtTheList(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        Optional<Position> list = InputDomain.of(sigs.get("probe"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none()).positions()
                .stream().filter(each -> each.path().toString().equals("n.postings")).findFirst();
        assertTrue(list.isPresent(), "the list is a position of the input");
        return list.get().unansweredQuestions().stream()
                .map(question -> question.rule().toString()).toList();
    }
}
