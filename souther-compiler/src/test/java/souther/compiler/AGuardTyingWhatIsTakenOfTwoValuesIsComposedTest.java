package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.CompositionBudget;
import souther.compiler.partition.CompositionRepertoire;
import souther.compiler.partition.DecisionRule;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.DecisionEvidence;
import souther.compiler.query.RuleRequirement;
import souther.compiler.query.RuleSettlement;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
            data Group = { deals: List<Deal> }
            data Rates = { rates: Map<String, Int>, since: Date, year: Int }
            data Priced = { n: Int }
            data Unpriced = { n: Int }

            behavior named : (deals: List<Deal>, groups: List<Group>, rates: Rates)
                    -> Priced | Unpriced
                constructs Priced, Unpriced

            let named (deals, groups, rates) = {
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

    /**
     * Exactly so many elements whose number taken of a value stands at a figure are chosen among
     * values built for that figure: the places the value itself turns at name none of them.
     */
    @Test
    void exactlySoManyElementsWhoseTakenNumberIsAtAFigureAreComposed() {
        for (String statement : List.of(
                "Date.day(d.on) == 5",
                "Date.month(d.on) == 3",
                "Date.year(d.on) == 1990",
                "Date.day(d.on) == Date.day(rates.since)",
                "String.length(d.currency) == 7",
                "Int.floorMod(d.amount, 7) == 3")) {
            assertEquals(List.of(), whatNothingCouldShow(
                    "List.length(List.filter(d -> " + statement + ", deals)) == 1"), statement);
        }
    }

    /**
     * One element holds one value, so what is taken of it at two places is taken of one value: a
     * date whose day is 5 and whose month is 3 is composed as a date, not as a day and a month.
     */
    @Test
    void numbersTakenOfOneValueAreComposedForTheOneValue() {
        assertEquals(List.of(), whatNothingCouldShow("List.length(List.filter(d -> "
                + "Date.day(d.on) == 5 && Date.month(d.on) == 3, deals)) == 1"));
        assertEquals(List.of(), whatNothingCouldShow("List.length(List.filter(d -> "
                + "String.length(d.currency) == 3 && Date.year(d.on) == 1990, deals)) == 2"));
    }

    /**
     * What is added up of the elements a statement of their own field keeps is added up of the
     * values that statement holds at: the form is taken there, and the elements are chosen there.
     */
    @Test
    void aTotalOfTheElementsAStatementOfTheirFieldKeepsIsComposed() {
        for (String kept : List.of("d.amount > 3", "d.amount >= 3", "d.amount < 3",
                "d.amount <= 3", "d.amount == 5")) {
            assertEquals(List.of(), whatNothingCouldShow("List.sum(List.map(d -> d.amount, "
                    + "List.filter(d -> " + kept + ", deals))) == 10"), kept);
        }
    }

    /**
     * How many elements the lists inside a list hold between them that meet a statement is a count
     * of all of them put end to end, whatever the statement reads of an element.
     */
    @Test
    void aCountOfTheElementsOfTheListsInsideAListIsComposed() {
        for (String statement : List.of("true", "d.amount == 5", "Date.day(d.on) == 5")) {
            String kept = statement.equals("true") ? "g.deals"
                    : "List.filter(d -> " + statement + ", g.deals)";
            for (String held : List.of("== 1", "== 2", ">= 3")) {
                assertEquals(List.of(), whatNothingCouldShow("List.length(List.flatMap(g -> "
                        + kept + ", groups)) " + held), statement + " " + held);
            }
        }
    }

    /**
     * Elements chosen by what they hold inside: how many they hold, whether some inside meets a
     * statement, how many inside do.
     */
    @Test
    void aCountOfTheElementsWhoseInnerContainerIsReadIsComposed() {
        for (String statement : List.of(
                "List.length(g.deals) == 2",
                "List.any(d -> d.amount == 5, g.deals)",
                "List.all(d -> d.amount == 5, g.deals)",
                "List.length(List.filter(d -> d.amount == 5, g.deals)) == 1")) {
            for (String held : List.of("== 1", "== 2", ">= 1")) {
                assertEquals(List.of(), whatNothingCouldShow("List.length(List.filter(g -> "
                        + statement + ", groups)) " + held), statement + " " + held);
            }
        }
    }

    /** Some or every element chosen by how many it holds inside that meet something. */
    @Test
    void someOrEveryElementWhoseInnerCountIsReadIsComposed() {
        String inner = "List.length(List.filter(d -> d.amount == 5, g.deals)) == 1";
        assertEquals(List.of(), whatNothingCouldShow("List.any(g -> " + inner + ", groups)"));
        assertEquals(List.of(), whatNothingCouldShow("List.all(g -> " + inner + ", groups)"));
    }

    private static final String BAGS = """
            module probe

            data Bag = { xs: List<Int> }
            data Priced = { n: Int }
            data Unpriced = { n: Int }

            behavior named : (bags: List<Bag>) -> Priced | Unpriced
                constructs Priced, Unpriced

            let named (bags) = {
                guard GUARD
                    else Unpriced { n = 0 }
                Priced { n = 1 }
            }
            """;

    /**
     * An inner container listed up to a figure is a search that stopped at it: what no listed size
     * meets is not shown to be met by no container.
     */
    @Test
    void aSizeThePartsAreNotListedAtIsAFigureTheSearchStoppedAtAndNotAnExclusion() {
        String guard = "List.length(List.filter(b -> List.length(List.filter("
                + "x -> x == 5, b.xs)) == 4, bags)) == 1";
        String model = BAGS.replace("GUARD", guard);
        assertEquals(List.of(), DecisionRulesTheSearchLeftUnsettled.excludedIn(model, "probe"));
        assertTrue(whatTheSearchSaid(model).contains(
                CompositionBudget.ELEMENTS_AN_INNER_CONTAINER_IS_LISTED_WITH.name()));
    }

    /**
     * A total over the elements a statement of their field keeps is solved only where the others
     * add nothing: elements the statement leaves are weighed too where they add a number, which is
     * said as a way this compiler does not write and not solved as if they added none.
     */
    @Test
    void aTotalWhoseOtherElementsAddANumberIsNotSolvedAsIfTheyAddedNone() {
        String model = DEALS.replace("GUARD", "List.sum(List.map(d -> "
                + "if d.amount > 3 then d.amount else 2, deals)) == 2");
        assertEquals(List.of(), DecisionRulesTheSearchLeftUnsettled.excludedIn(model, "probe"));
        assertTrue(whatTheSearchSaid(model).contains(
                CompositionRepertoire.ELEMENTS_A_COMPUTED_TOTAL_IS_SOLVED_FOR.name()));
    }

    /** What the search said of every rule it left unsettled, in the words it keeps. */
    private static String whatTheSearchSaid(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        StringBuilder said = new StringBuilder();
        Map<String, DecisionEvidence> decisions =
                compilation.db().ask(new Adequacy.Decides("probe")).value();
        for (String behavior : decisions.keySet()) {
            compilation.db().ask(new Adequacy.DecisionSearch("probe", behavior)).value()
                    .forEach((rule, across) -> {
                        RuleSettlement settlement = across.answer().settlement();
                        if (settlement.requirement() instanceof RuleRequirement.Unsettled) {
                            said.append(settlement.search()).append(settlement.account());
                        }
                    });
        }
        return said.toString();
    }

    /** The rules of the decision no search could settle. */
    private static List<DecisionRule> whatNothingCouldShow(String guard) {
        return DecisionRulesTheSearchLeftUnsettled.notShownIn(DEALS.replace("GUARD", guard),
                "probe");
    }
}
