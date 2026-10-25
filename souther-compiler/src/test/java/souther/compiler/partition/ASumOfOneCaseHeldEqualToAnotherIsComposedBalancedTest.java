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
        return """
                module demo

                import List ( fold, length )

                data Amount = Decimal
                    invariant value >= 0.0m
                data Side = Debit | Credit
                data Posting = { side: Side, amount: Amount }

                let sideTotal (wanted: Side, postings: List<Posting>): Decimal =
                    fold((acc, p) -> if p.side == wanted then Decimal.add(acc, p.amount.value) else acc,
                         0.0m, postings)

                data N = { postings: List<Posting> }
                    invariant enough = length(postings) >= %d
                    invariant balanced =
                        Decimal.compare(sideTotal(Debit, postings), sideTotal(Credit, postings)) == 0
                """.formatted(least);
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
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule record = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, "demo"), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        Partitions.FieldsChosen chosen =
                Partitions.fieldsOf(record, record, reading, Set.of(), Map.of());
        assertNotNull(chosen.fields(), "the record is one something can be composed of");
        return chosen;
    }
}
