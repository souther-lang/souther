package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.DecisionRule;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A guard tying a key of a map to a value a row holds, or a part of a date to a part of another
 * date or to a number, is composed: a row is found that meets it and one that does not.
 *
 * <p>What is taken of a value is a place of its own, and a statement over it is a demand on that
 * place: it is met by choosing the value, as a statement over the value itself is.
 */
class AGuardTyingWhatIsTakenOfTwoValuesIsComposedTest {

    private static final String DEALS = """
            module probe

            data Deal = { currency: String, amount: Int, on: Date }
            data Rates = { rates: Map<String, Int>, since: Date, year: Int }
            data Priced = { n: Int }
            data Unpriced = { n: Int }

            behavior named : (deals: List<Deal>, rates: Rates) -> Priced | Unpriced
                constructs Priced, Unpriced

            let named (deals, rates) = {
                guard GUARD
                    else Unpriced { n = 0 }
                Priced { n = 1 }
            }
            """;

    private static final String KEYED = "Map.containsKey(d.currency, rates.rates)";

    private static final String SAME_YEAR = "Date.year(d.on) == Date.year(rates.since)";

    private static final String BEFORE_YESTERDAY =
            "Date.day(Date.addDays(0 - 1, d.on)) == Date.day(rates.since)";

    @Test
    void aKeyTiedToAValueTheRowHoldsIsComposedForAnyAndForNoneOfTheElements() {
        assertEquals(List.of(), whatNothingCouldShow(
                "List.length(List.filter(d -> " + KEYED + ", deals)) == 1"));
        assertEquals(List.of(), whatNothingCouldShow(
                "List.length(List.filter(d -> Bool.not(" + KEYED + "), deals)) == 1"));
        assertEquals(List.of(), whatNothingCouldShow("List.any(d -> " + KEYED + ", deals)"));
        assertEquals(List.of(), whatNothingCouldShow("List.all(d -> " + KEYED + ", deals)"));
    }

    @Test
    void aPartOfADateTiedToAPartOfAnotherOrToANumberIsComposed() {
        assertEquals(List.of(), whatNothingCouldShow(
                "List.length(List.filter(d -> " + SAME_YEAR + ", deals)) == 2"));
        assertEquals(List.of(), whatNothingCouldShow(
                "List.length(List.filter(d -> Date.year(d.on) == rates.year, deals)) == 1"));
        assertEquals(List.of(), whatNothingCouldShow("List.all(d -> " + SAME_YEAR + ", deals)"));
        assertEquals(List.of(), whatNothingCouldShow("List.length(List.filter(d -> "
                + "Date.month(d.on) == Date.month(rates.since), deals)) == List.length(deals)"));
    }

    @Test
    void aPartOfADateMovedBeforeItIsTakenIsComposedAsTheDateIsNot() {
        assertEquals(List.of(), whatNothingCouldShow(
                "List.length(List.filter(d -> " + BEFORE_YESTERDAY + ", deals)) >= 1"));
        assertEquals(List.of(), whatNothingCouldShow(
                "List.length(List.filter(d -> " + BEFORE_YESTERDAY + ", deals)) == 0"));
        assertEquals(List.of(), whatNothingCouldShow(
                "List.all(d -> " + BEFORE_YESTERDAY + ", deals)"));
    }

    /** The rules of the decision no search could settle. */
    private static List<DecisionRule> whatNothingCouldShow(String guard) {
        return DecisionRulesTheSearchLeftUnsettled.notShownIn(DEALS.replace("GUARD", guard),
                "probe");
    }
}
