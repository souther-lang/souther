package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Symbols;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A list whose rules hold the total of one case of a field equal to the total of another is
 * composed with the totals equal and neither of them nought, however many elements the rules ask
 * for.
 *
 * <p>An element at a case adds as many units as the other case has elements, so the two totals are
 * the product of the two counts. Composed element by element against the rules of the element
 * alone, the totals met only where the elements happened to cancel, and an empty side is a total of
 * nought that balances anything.
 */
class ASumOfOneCaseHeldEqualToAnotherIsComposedBalancedTest {

    private static final Pattern ELEMENT =
            Pattern.compile("side = (\\w+), amount = Amount\\(([0-9.]+)m\\)");

    private static String journal(int least) {
        return journal(least, "value >= 0.0m");
    }

    private static String journal(int least, String amountRule) {
        return """
                module demo

                import List ( fold, length )

                data Amount = Decimal
                    invariant %s
                data Side = Debit | Credit
                data Posting = { side: Side, amount: Amount }

                let sideTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.amount.value) else acc,
                         0.0m, postings)

                data N = { postings: List<Posting> }
                    invariant enough = length(postings) >= %d
                    invariant balanced =
                        Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 0
                """.formatted(amountRule, least);
    }

    /**
     * Every amount is one the element's type admits, whatever the type holds it to.
     *
     * <p>The unit is a whole number inside what the amount admits and so is every multiple of it
     * that is added, so a type that admits nothing below ten is given amounts from ten up and not
     * the one a count would have given it.
     */
    @Test
    void everyAmountIsOneTheAmountTypeAdmits() {
        for (int least : new int[] {2, 3, 5}) {
            String list = composed(journal(least, "value >= 10.0m")).fields().get("postings").text();
            Matcher found = ELEMENT.matcher(list);
            Map<String, BigDecimal> totals = new LinkedHashMap<>();
            while (found.find()) {
                BigDecimal amount = new BigDecimal(found.group(2));
                assertTrue(amount.compareTo(BigDecimal.TEN) >= 0, list);
                totals.merge(found.group(1), amount, BigDecimal::add);
            }
            assertEquals(0, totals.get("Debit").compareTo(totals.get("Credit")), list);
        }
    }

    /** A type that admits too little for the sides to balance is no list, and no list is offered. */
    @Test
    void anAmountTypeThatAdmitsLessThanTheSidesNeedIsNotBuilt() {
        assertNull(composedOrNot(journal(3, "value >= 0.0m && value <= 1.0m")).fields(),
                "three postings need an amount of two on one side");
    }

    /** A count past what a proposal may hold is not built, and is not built a little at a time. */
    @Test
    void aCountPastWhatAProposalMayHoldIsNotBuilt() {
        assertNull(composedOrNot(journal(100_000_000)).fields());
    }

    @Test
    void theTotalsOfTheTwoCasesAreEqualAndNotNoughtWhateverTheCount() {
        for (int least : new int[] {2, 3, 4, 5, 7}) {
            String list = composed(journal(least)).fields().get("postings").text();
            Map<String, BigDecimal> totals = new LinkedHashMap<>();
            Matcher found = ELEMENT.matcher(list);
            int elements = 0;
            while (found.find()) {
                totals.merge(found.group(1), new BigDecimal(found.group(2)), BigDecimal::add);
                elements++;
            }
            assertEquals(Set.of("Debit", "Credit"), totals.keySet(),
                    "both sides hold an element, or one side's total is nought: " + list);
            assertEquals(0, totals.get("Debit").compareTo(totals.get("Credit")), list);
            assertTrue(totals.get("Debit").signum() > 0, list);
            assertTrue(elements >= least, "at least " + least + " postings: " + list);
        }
    }

    private static Partitions.FieldsChosen composed(String source) {
        Partitions.FieldsChosen chosen = composedOrNot(source);
        assertNotNull(chosen.fields(), "the record is one something can be composed of");
        return chosen;
    }

    private static Partitions.FieldsChosen composedOrNot(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule record = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, "demo"), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        return Partitions.fieldsOf(record, record, reading, Set.of(), Map.of());
    }
}
