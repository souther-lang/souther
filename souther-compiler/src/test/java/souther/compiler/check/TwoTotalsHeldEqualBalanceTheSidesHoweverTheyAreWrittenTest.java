package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two totals of one list at two cases held equal balance the sides, however the equality is
 * written: the totals themselves held equal, the sign of their order held at nought, the same under
 * a denial of its opposite, and a total walked over what a filter kept by the case rather than
 * adding under the case.
 *
 * <p>The comparison of the order's sign at nought is the oracle: each spelling asks of the list what
 * it asks and is accounted for as it is. A difference held at nought or at something else, a sign
 * held at one, and a walk both filtered and conditioned are other rules, and are the controls.
 */
class TwoTotalsHeldEqualBalanceTheSidesHoweverTheyAreWrittenTest {

    private static final String ORACLE =
            "Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 0";

    private record Read(Map<RuleKey, List<SidesBalanced.Requirement>> balanced,
                        boolean accounted) {}

    private static Read read(String rule) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                import List ( fold, filter )

                data Amount = Decimal
                    invariant value >= 0.0m
                data Side = Debit | Credit
                data Posting = { side: Side, amount: Amount }

                let sideTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.amount.value) else acc,
                         0.0m, postings)

                let keptTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> Decimal.add(acc, p.amount.value), 0.0m,
                         filter(p -> p.side == wanted, postings))

                let bothTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.amount.value) else acc,
                         0.0m, filter(p -> p.side == wanted, postings))

                data N = { postings: List<Posting> }
                    invariant %s
                """.formatted(rule), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey("demo", "N"));
        FieldDomains domains = FieldDomains.of(named,
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY));
        return new Read(SidesBalanced.writtenOn(named, rules), domains.accounting().values()
                .stream().allMatch(each -> each.unaccounted().isEmpty()));
    }

    @Test
    void eachSpellingOfTheEqualityBalancesWhatTheOracleBalances() {
        Read oracle = read(ORACLE);
        assertFalse(oracle.balanced().isEmpty(), "the oracle balances the list");
        assertTrue(oracle.accounted(), "and is accounted for");
        for (String rule : List.of(
                "sideTotal(Debit, postings) == sideTotal(Credit, postings)",
                "Bool.not(Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings))"
                        + " /= 0)",
                "Decimal.compare(keptTotal(Debit, postings), keptTotal(Credit, postings)) == 0",
                "Decimal.compare(sideTotal(Debit, postings), keptTotal(Credit, postings)) == 0")) {
            assertEquals(oracle, read(rule), rule);
        }
    }

    /**
     * And the difference held at nought is one of them: the library says a decimal's difference
     * may have no place, so it stops on totals their equality does not, and there it is another
     * rule.
     */
    @Test
    void anotherRuleOverTheTotalsBalancesNothing() {
        for (String rule : List.of(
                "Decimal.subtract(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 0.0m",
                "Decimal.subtract(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 1.0m",
                "Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 1",
                "Decimal.compare(bothTotal(Debit, postings), bothTotal(Credit, postings)) == 0",
                "Decimal.compare(sideTotal(Debit, postings), sideTotal(Debit, postings)) == 0")) {
            assertEquals(Map.of(), read(rule).balanced(), rule);
        }
    }
}
