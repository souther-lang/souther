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
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
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
 * composed with the totals equal, whatever the element's number admits and however many elements
 * the rules ask for.
 *
 * <p>The numbers an element adds are numbers its own type admits, taken from the type and not made
 * beside it, and the totals are equal because numbers were found that make them so. A type that
 * admits a set of numbers is balanced from that set, one that admits only negative numbers or only
 * nought is balanced by them, and a type whose numbers balance nothing gives no list.
 */
class ASumOfOneCaseHeldEqualToAnotherIsComposedBalancedTest {

    private static final Pattern ELEMENT =
            Pattern.compile("side = (\\w+), amount = Amount\\((-?[0-9.]+)m\\)");

    private static String journal(int least) {
        return journal(least, "value >= 0.0m", "");
    }

    private static String journal(int least, String amountRule, String more) {
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
                    %s
                """.formatted(amountRule, least, more);
    }

    /** The amounts of each side of a composed list, and how many elements it has. */
    private record Sides(Map<String, List<BigDecimal>> amounts, int elements) {

        BigDecimal total(String side) {
            return amounts.getOrDefault(side, List.of()).stream().reduce(BigDecimal.ZERO,
                    BigDecimal::add);
        }
    }

    private static Sides sidesOf(String list) {
        Map<String, List<BigDecimal>> amounts = new LinkedHashMap<>();
        Matcher found = ELEMENT.matcher(list);
        int elements = 0;
        while (found.find()) {
            amounts.computeIfAbsent(found.group(1), _ -> new ArrayList<>())
                    .add(new BigDecimal(found.group(2)));
            elements++;
        }
        return new Sides(amounts, elements);
    }

    @Test
    void theTotalsOfTheTwoCasesAreEqualAndNotNoughtWhateverTheCount() {
        for (int least : new int[] {2, 3, 4, 5, 7, 9, 20}) {
            String list = composed(journal(least)).fields().get("postings").text();
            Sides sides = sidesOf(list);
            assertEquals(Set.of("Debit", "Credit"), sides.amounts().keySet(),
                    "both sides hold an element, or one side's total is nought: " + list);
            assertEquals(0, sides.total("Debit").compareTo(sides.total("Credit")), list);
            assertTrue(sides.total("Debit").signum() > 0, list);
            assertTrue(sides.elements() >= least, "at least " + least + " postings: " + list);
        }
    }

    /** Every amount is one the amount type admits, whatever the type holds it to. */
    @Test
    void everyAmountIsOneTheAmountTypeAdmits() {
        for (int least : new int[] {2, 3, 5}) {
            Sides sides = sidesOf(composed(journal(least, "value >= 10.0m", ""))
                    .fields().get("postings").text());
            sides.amounts().values().forEach(each -> each.forEach(amount ->
                    assertTrue(amount.compareTo(BigDecimal.TEN) >= 0, amount.toString())));
            assertEquals(0, sides.total("Debit").compareTo(sides.total("Credit")));
        }
    }

    /**
     * A type that admits three numbers and not the one between two of them is balanced from the
     * three: one debit of four against credits of one and three, which no one number repeated makes.
     */
    @Test
    void aTypeThatAdmitsASetOfNumbersIsBalancedFromThatSet() {
        String list = composed(journal(3,
                "value == 1.0m || value == 3.0m || value == 4.0m", ""))
                .fields().get("postings").text();
        Sides sides = sidesOf(list);

        sides.amounts().values().forEach(each -> each.forEach(amount -> assertTrue(
                Set.of(1, 3, 4).contains(amount.intValueExact()), list)));
        assertEquals(0, sides.total("Debit").compareTo(sides.total("Credit")), list);
    }

    /** Positive numbers are what is tried first and no condition: a side of negatives balances. */
    @Test
    void aTypeThatAdmitsOnlyNegativeNumbersIsBalancedByThem() {
        String list = composed(journal(3, "value < 0.0m", "")).fields().get("postings").text();
        Sides sides = sidesOf(list);

        sides.amounts().values().forEach(each -> each.forEach(amount ->
                assertTrue(amount.signum() < 0, list)));
        assertEquals(0, sides.total("Debit").compareTo(sides.total("Credit")), list);
    }

    @Test
    void aTypeThatAdmitsOnlyNoughtIsBalancedByNought() {
        String list = composed(journal(2, "value == 0.0m", "")).fields().get("postings").text();
        Sides sides = sidesOf(list);

        assertEquals(2, sides.elements(), list);
        assertEquals(0, sides.total("Debit").signum(), list);
        assertEquals(0, sides.total("Credit").signum(), list);
    }

    /**
     * Three elements of the one number there is cannot balance, and four can: the least the rules
     * ask for is where the walk starts, and the list of four is a list the rules allow.
     */
    @Test
    void aCountThatTheNumbersCannotBalanceIsPassedForOneThatTheyCan() {
        Sides sides = sidesOf(composed(journal(3, "value == 1.0m", "")).fields()
                .get("postings").text());

        assertEquals(4, sides.elements());
        assertEquals(0, sides.total("Debit").compareTo(sides.total("Credit")));
        assertEquals(2, sides.amounts().get("Debit").size());
    }

    /** Where the rules leave no count the numbers balance, no list is offered. */
    @Test
    void aTypeWhoseNumbersBalanceNoCountTheRulesLeaveIsNotBuilt() {
        // Three elements and no more: one debit and two credits, and a 1 balances neither.
        assertNull(composedOrNot(journal(3, "value == 1.0m",
                "invariant atMost = length(postings) <= 3")).fields());
    }


    /** A count past what a proposal may hold is not built, and is not built a little at a time. */
    @Test
    void aCountPastWhatAProposalMayHoldIsNotBuilt() {
        assertNull(composedOrNot(journal(100_000_000)).fields());
    }

    /**
     * Elements that are also to be kept apart are not made by this: they differ in their side and
     * their amount and nothing else, and what keeps them apart in the rest is not asked. A list
     * of a debit of four against credits of one and three is kept apart and balanced both, so this
     * is a combination left unbuilt and not a type with no such list.
     */
    @Test
    void aListThatIsAlsoKeptApartIsNotBuilt() {
        assertNull(composedOrNot(journal(3, "value >= 0.0m",
                "invariant apart = List.allDistinctBy(.amount, postings)")).fields());
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
