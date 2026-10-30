package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many different values the elements meeting a statement hold at one place of each is a
 * number a rule can draw a line on ({@link Quantity.HowManyDifferentMeet}), and a row stands on
 * that line where that many values are held by elements meeting it.
 *
 * <p>Written over a filter, the statement is asked of each element: a value is counted where some
 * element holding it meets it. Written over the entries a fold filed under the value, it is asked
 * of what the elements of each value come to. {@code 10} and {@code -10} under one currency tell
 * the two apart: one of them is above nought, and their total is not.
 *
 * <p>Every example below is run, so the answer it writes is what the language computes; which point
 * it hits is what the line reads of it. The two are the same row.
 */
class HowManyDifferentValuesMeetingAStatementIsALineOnTheCountTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String DECLARED = """
            data Forecast = { currency: String, amount: Int }

            let filed (cs: List<String>): Map<String, Int> =
                List.fold((acc, c) -> Map.updateOrInsert(c, 1, n -> n + 1, acc), Map.empty, cs)

            let totalsOf (fs: List<Forecast>): Map<String, Int> =
                List.fold((acc, f) -> Map.updateOrInsert(f.currency, f.amount,
                    n -> n + f.amount, acc), Map.empty, fs)

            """;

    private static final String HEAD = "module probe\n\n" + DECLARED + """
            behavior f : (fs: List<Forecast>) -> Int
            let f (fs) = if %s then 1 else 0
            """;

    private static final String OF_EACH_ELEMENT =
            "#different fs [fs[*].currency] where [fs[*].amount > 0]";

    private static final String OF_EACH_VALUE =
            "#different fs [fs[*].currency] where [total(fs[*].amount by currency) > 0]";

    /** The forecasts of every desk, which a flattening puts end to end. */
    private static final String ACROSS = "module probe\n\n" + DECLARED + """
            data Desk = { forecasts: List<Forecast> }

            behavior f : (ds: List<Desk>) -> Int
            let f (ds) = if %s then 1 else 0
            """;

    private static final String ACROSS_OF_EACH_ELEMENT = "#different ds"
            + " [ds[*].forecasts[*].currency] where [ds[*].forecasts[*].amount > 0]";

    private static final String ACROSS_OF_EACH_VALUE = "#different ds"
            + " [ds[*].forecasts[*].currency] where"
            + " [total(ds[*].forecasts[*].amount by currency) > 0]";

    /** However the different values of the elements a filter kept are counted, one count. */
    @Test
    void everyWayOfCountingTheValuesAFilterKeptIsOneCount() {
        for (String count : List.of(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))",
                "List.length(List.distinct(List.map(.currency,"
                        + " List.filter(f -> f.amount > 0, fs))))",
                "Set.size(List.fold((acc, f) -> Set.insert(f.currency, acc), Set.empty,"
                        + " List.filter(f -> f.amount > 0, fs)))",
                "Map.size(filed(List.map(.currency, List.filter(f -> f.amount > 0, fs))))")) {
            JsonNode line = only(differentCounts(reportOf(HEAD.formatted(count + " == 1"))));
            assertEquals(OF_EACH_ELEMENT, line.at("/lineId/target/quantity/counted").asString(),
                    count);
        }
    }

    /** And how many entries of a fold's map a statement keeps is a count of the values whose
     *  total meets it. */
    @Test
    void theEntriesAStatementKeepsOfAFoldsMapAreTheValuesWhoseTotalMeetsIt() {
        JsonNode line = only(differentCounts(reportOf(HEAD.formatted(
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs))) == 1"))));
        assertEquals(OF_EACH_VALUE, line.at("/lineId/target/quantity/counted").asString());
    }

    /**
     * Asked of each element, {@code 10} under a currency keeps the currency whatever else is under
     * it, and two elements of one currency are one value.
     */
    @Test
    void aValueIsCountedWhereSomeElementHoldingItMeetsTheStatement() {
        JsonNode line = only(differentCounts(reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == 1") + """
                example f
                    | "one of two above nought" : ([Forecast { currency = "USD", amount = 10 },
                        Forecast { currency = "USD", amount = -10 }]) -> 1
                """)));
        assertTrue(pointAt(line, "on").path("hit").asBoolean(), line::toString);

        JsonNode twice = only(differentCounts(reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == 1") + """
                example f
                    | "two of one currency" : ([Forecast { currency = "USD", amount = 10 },
                        Forecast { currency = "USD", amount = 20 }]) -> 1
                """)));
        assertTrue(pointAt(twice, "on").path("hit").asBoolean(), twice::toString);

        JsonNode two = only(differentCounts(reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == 1") + """
                example f
                    | "two currencies" : ([Forecast { currency = "USD", amount = 10 },
                        Forecast { currency = "EUR", amount = 20 }]) -> 0
                """)));
        assertFalse(pointAt(two, "on").path("hit").asBoolean(), two::toString);
        assertTrue(pointsAt(two, "off").stream().anyMatch(off -> off.path("hit").asBoolean()
                && "2".equals(off.path("against").asString())), two::toString);
    }

    /**
     * Asked of what the elements of each value come to, {@code 10} and {@code -10} under one
     * currency total nought and keep nothing, though one of them is above nought on its own.
     */
    @Test
    void aValueIsCountedWhereWhatItsElementsComeToMeetsTheStatement() {
        JsonNode cancelled = only(differentCounts(reportOf(HEAD.formatted(
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs))) == 1") + """
                example f
                    | "one of two above nought" : ([Forecast { currency = "USD", amount = 10 },
                        Forecast { currency = "USD", amount = -10 }]) -> 0
                """)));
        assertFalse(pointAt(cancelled, "on").path("hit").asBoolean(), cancelled::toString);
        assertTrue(pointsAt(cancelled, "off").stream().anyMatch(off -> off.path("hit").asBoolean()
                && "0".equals(off.path("against").asString())), cancelled::toString);

        JsonNode kept = only(differentCounts(reportOf(HEAD.formatted(
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs))) == 1") + """
                example f
                    | "below nought on its own" : ([Forecast { currency = "USD", amount = 20 },
                        Forecast { currency = "USD", amount = -10 },
                        Forecast { currency = "EUR", amount = -5 }]) -> 1
                """)));
        assertTrue(pointAt(kept, "on").path("hit").asBoolean(), kept::toString);
    }

    /** How often a value occurs is what its elements come to as well: a currency held twice is
     *  kept by a statement that it is held twice, and one held once is not. */
    @Test
    void aValueIsCountedWhereHowOftenItOccursMeetsTheStatement() {
        JsonNode line = only(differentCounts(reportOf(HEAD.formatted(
                "Map.size(Map.filterEntries((_, n) -> n >= 2, filed(List.map(.currency, fs))))"
                        + " == 1") + """
                example f
                    | "one currency twice" : ([Forecast { currency = "USD", amount = 1 },
                        Forecast { currency = "EUR", amount = 1 },
                        Forecast { currency = "USD", amount = 1 }]) -> 1
                """)));
        assertEquals("#different fs [fs[*].currency] where [multiplicity(fs[*].currency) >= 2]",
                line.at("/lineId/target/quantity/counted").asString());
        assertTrue(pointAt(line, "on").path("hit").asBoolean(), line::toString);
    }

    /**
     * Every point of a line on either count has a row composed for it, two values above one held
     * by elements of different values, and below none is no count at all. Where elements of one
     * value meet the statement more than one way — on either side of five — two of them are
     * still one value, and two values are two elements of different ones.
     */
    @Test
    void everyPointOfALineOnEitherCountHasARowComposedForIt() {
        for (String count : List.of(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))",
                "Set.size(Set.fromList(List.map(.currency,"
                        + " List.filter(f -> f.amount > 0 && f.amount /= 5, fs))))",
                "Map.size(Map.filterEntries((_, n) -> n > 0, totalsOf(fs)))",
                "Map.size(Map.filterEntries((_, n) -> n >= 2, filed(List.map(.currency, fs))))")) {
            for (String against : List.of(" >= 2", " == 1")) {
                JsonNode line = only(differentCounts(reportOf(HEAD.formatted(count + against))));
                for (JsonNode item : line.path("items")) {
                    if (item.has("notOwed")) {
                        assertEquals("no_value_can_stand_there", item.path("notOwed").asString(),
                                item::toString);
                        continue;
                    }
                    List<String> because = new ArrayList<>();
                    item.path("writableBecause").forEach(each -> because.add(each.asString()));
                    assertTrue(item.path("knownWritable").asBoolean()
                            && because.contains("a_value_was_built"),
                            () -> count + against + ": " + item);
                }
            }
        }
    }

    /**
     * A value counted by what the elements under it come to may take more than one of them: a
     * currency held twice, two amounts under one currency totalling nought where no amount is
     * nought, or a total of a hundred and fifty where no amount is above a hundred. The rows
     * composed for such a line
     * hold as many as it takes, and answer as their points say.
     */
    @Test
    void aValueIsComposedWithAsManyElementsUnderItAsWhatTheyComeToTakes() {
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Map.size(Map.filterEntries((_, n) -> n >= 2,
                    filed(List.map(.currency, fs)))) == 1 then 1 else 0
                """, "f/#different fs [fs[*].currency] where [multiplicity(fs[*].currency) >= 2]");
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if List.all(f -> f.amount /= 0, fs) then
                    if Map.size(Map.filterEntries((_, n) -> n == 0, totalsOf(fs))) == 1 then 1
                    else 0
                    else 2
                """, "f/#different fs [fs[*].currency] where"
                + " [total(fs[*].amount by currency) == 0]");
        // A total no one element reaches is reached by several, each a share of it.
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if List.all(f -> f.amount <= 100, fs) then
                    if Map.size(Map.filterEntries((_, n) -> n == 150, totalsOf(fs))) == 1 then 1
                    else 0
                    else 2
                """, "f/#different fs [fs[*].currency] where"
                + " [total(fs[*].amount by currency) == 150]");
    }

    /**
     * How often the value at a place inside an element occurs is a number of the element, and a
     * row at its line holds that value under as many elements as the line asks, chosen among the
     * values each element is read at whole.
     */
    @Test
    void howOftenAValueInsideAnElementOccursIsComposedWithThatManyElementsUnderIt() {
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Map.size(Map.filterEntries((_, n) -> n >= 2,
                    filed(List.map(.currency, fs)))) >= 1 then 1 else 0
                """, "f/multiplicity(fs[*].currency)");
    }

    /**
     * Where the way to a line on how often a value occurs leaves the container one size, its rows
     * hold that many: a value twice in three elements, and three values once each, though the
     * smallest container a value occurs twice in is two.
     */
    @Test
    void howOftenAValueOccursIsComposedAtTheSizeTheWayToItLeaves() {
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (cs: List<String>) -> Int
                let f (cs) = if List.length(cs) == 3 then
                    if Map.size(Map.filterEntries((_, n) -> n >= 2, filed(cs))) >= 1 then 1
                    else 0
                    else 2
                """, "f/multiplicity(cs[*])");
    }

    /**
     * How often a value occurs among the elements a statement keeps is of those it keeps, and the
     * elements holding the value may be more: where every element is one currency and there are
     * two of them, the currency kept once is held by one element above nought and one at or below
     * it.
     */
    @Test
    void aValueKeptOnceMayBeHeldByElementsTheStatementDoesNotKeep() {
        String occurrences = "occurrences(fs[*].currency kept by fs meeting Affine[form="
                + "LinearForm[constant=0, coefs={fs[*].amount=1}], proposition=GT])";
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if List.all(f -> f.currency == "USD", fs)
                        && List.length(fs) == 2 then
                    if Map.size(Map.filterEntries((_, n) -> n == 1,
                        filed(List.map(.currency, List.filter(f -> f.amount > 0, fs))))) >= 1
                    then 1 else 0
                    else 2
                """, "f/" + occurrences, "2 < " + occurrences);
    }

    /**
     * Elements meeting the statement may share a value: where every element is above nought and
     * one currency is counted, two elements are two of that currency. And a value some elements
     * must not hold is held by others where only they can hold it — two currencies kept and three
     * elements, one of them the `"x"` that only an element at or below nought is kept out at.
     */
    @Test
    void aLineUnderTheCountIsComposedWithElementsSharingAValueWhereItTakesThem() {
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if List.all(f -> f.amount > 0, fs) then
                    if Set.size(Set.fromList(List.map(.currency,
                        List.filter(f -> f.amount > 0, fs)))) == 1 then
                        if List.length(fs) == 2 then 1 else 0
                    else 2
                    else 3
                """, "f/List.length(fs)", "0 <= List.length(fs) < 1");
        everyRowComposedAnswersAsItsPointSays(DECLARED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Set.size(Set.fromList(List.map(.currency,
                    List.filter(f -> f.currency /= "x" || f.amount > 0, fs)))) == 2 then
                    if List.length(fs) == 3 then 1 else 0
                    else 2
                """, "f/List.length(fs)", "0 <= List.length(fs) < 2");
    }

    /**
     * Asked of each value, a statement has to answer alike for every element holding it. Which of
     * them is the last to hold it reads no place but the value's, and answers differently for the
     * first and the last of them, so it is refused; whether the value is there at all is not.
     */
    @Test
    void aStatementTurningOnWhichElementHoldsAValueIsNoStatementOfEachValue() {
        DecisionSubject.AnInput fs = new DecisionSubject.AnInput(TermPath.of("fs"));
        DecisionSubject.AnInput currency = new DecisionSubject.AnInput(
                TermPath.of("fs").element().then("currency"));
        Quantity.HowManyDifferentMeet.Selection last =
                new Quantity.HowManyDifferentMeet.Selection.OfEachValue(
                        new Proposition.LastToHold(fs, currency, true));
        Quantity.TheValue value = new Quantity.TheValue.AtAPlace(currency);
        assertThrows(IllegalArgumentException.class,
                () -> new Quantity.HowManyDifferentMeet(fs, value, last));
        assertNull(Quantity.HowManyDifferentMeet.of(fs, value, last));
        assertNotNull(Quantity.HowManyDifferentMeet.of(fs, value,
                new Quantity.HowManyDifferentMeet.Selection.OfEachValue(
                        new Proposition.Present(currency, true))));
    }

    /**
     * Across the lists inside the elements of a list, the elements holding one value stand in
     * different elements of the outer list, so a statement of each value reading a place of the
     * outer element answers for each of them apart and is refused; one reading only the value is
     * not.
     */
    @Test
    void aStatementOfEachValueAcrossTheListsReadsNothingOfTheElementHoldingOne() {
        TermPath desk = TermPath.of("ds").element();
        DecisionSubject.AnInput ds = new DecisionSubject.AnInput(TermPath.of("ds"));
        DecisionSubject.AnInput currency = new DecisionSubject.AnInput(
                desk.then("forecasts").element().then("currency"));
        Proposition present = new Proposition.Present(currency, true);
        Quantity.HowManyDifferentMeet.Selection.OfEachValue alone =
                new Quantity.HowManyDifferentMeet.Selection.OfEachValue(present);
        Quantity.TheValue value = new Quantity.TheValue.AtAPlace(currency);
        assertNotNull(Quantity.HowManyDifferentMeet.of(ds, value, alone));
        assertTrue(Quantity.HowManyDifferentMeet.of(ds, value, alone).across());
        Quantity.HowManyDifferentMeet.Selection.OfEachValue withTheDesk =
                new Quantity.HowManyDifferentMeet.Selection.OfEachValue(new Proposition.All(
                        List.of(present, new Proposition.Present(new DecisionSubject.AnInput(
                                desk.then("floor")), true))));
        assertNull(Quantity.HowManyDifferentMeet.of(ds, value, withTheDesk));
    }

    /**
     * A line reached only where the count is one has rows composed for it holding one value kept
     * by the statement, as a line reached under a count of the elements does.
     */
    @Test
    void aLineReachedWhereTheCountIsOneHasRowsComposedForItHoldingOneValue() {
        JsonNode report = reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == 1 && List.length(fs) >= 3"));
        JsonNode length = null;
        for (JsonNode each : behaviorOf(report).at("/partition/boundaries")) {
            if ("f/List.length(fs)".equals(each.path("axis").asString())) {
                length = each;
            }
        }
        assertTrue(length != null, report::toString);
        for (JsonNode item : length.path("items")) {
            assertTrue(item.path("knownWritable").asBoolean(), item::toString);
        }
    }

    /**
     * A count recognised that no line can be drawn on — the different values of one container
     * against those of another — is a rule nobody read, and no row is offered for it.
     */
    @Test
    void aCountNoLineIsDrawnOnIsStillARuleNobodyRead() {
        JsonNode report = reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " == Set.size(Set.fromList(List.map(.currency, fs)))"));
        assertEquals(List.of(), differentCounts(report));
        assertTrue(behaviorOf(report).path("weakening").toString().contains("rule_unread"),
                report::toString);
    }

    /**
     * What keeps an element, said of the elements of the container it keeps from, says nothing of
     * one element: whether some value occurs twice among them is the same for each. The values it
     * keeps are those of all of them or of none, which is no count a line is drawn on, and the
     * reading says so rather than stopping.
     */
    @Test
    void aStatementOfEveryElementKeepingOneIsNoCountOfTheValuesItKeeps() {
        JsonNode report = reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f ->"
                        + " Map.size(Map.filterEntries((_, n) -> n >= 2,"
                        + " filed(List.map(.currency, fs)))) >= 1, fs)))) == 1"));
        assertEquals(List.of(), differentCounts(report));
        assertTrue(behaviorOf(report).path("weakening").toString().contains("rule_unread"),
                report::toString);
    }

    /**
     * The comparison the filter's closure writes is read where it is written, as its own line on
     * the element's number, and the count beside it leaves nothing of the input unread.
     */
    @Test
    void theClosuresComparisonIsItsOwnLineAndTheCountLeavesNothingUnread() {
        JsonNode report = reportOf(HEAD.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0, fs))))"
                        + " >= 2"));
        JsonNode behavior = behaviorOf(report);
        List<String> axes = new ArrayList<>();
        behavior.at("/partition/boundaries").forEach(each -> axes.add(each.path("axis")
                .asString()));
        assertTrue(axes.contains("f/fs[*].amount"), axes::toString);
        assertFalse(behavior.path("weakening").toString().contains("rule_unread"),
                behavior.path("weakening")::toString);
        List<String> unread = new ArrayList<>();
        behavior.at("/partition/notRead").forEach(each -> unread.add(each.path("position")
                .asString() + " " + each.path("reason").asString()));
        assertEquals(List.of("fs[*].amount rule_about_a_run"), unread);
    }

    /**
     * Over the lists inside the elements of a list put end to end, the different values of the
     * elements a filter kept are one count however it is written: the filter above the flattening
     * or inside its closure, a map above it, a fold gathering the values. And a fold filing the
     * elements of all of the lists under their keys is the values whose total meets what keeps an
     * entry.
     */
    @Test
    void everyWayOfCountingTheValuesKeptAcrossTheListsOfAFlatteningIsOneCount() {
        for (String count : List.of(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0,"
                        + " List.flatMap(d -> d.forecasts, ds)))))",
                "Set.size(Set.fromList(List.map(.currency, List.flatMap(d ->"
                        + " List.filter(f -> f.amount > 0, d.forecasts), ds))))",
                "Set.size(List.fold((acc, f) -> Set.insert(f.currency, acc), Set.empty,"
                        + " List.filter(f -> f.amount > 0, List.flatMap(d -> d.forecasts, ds))))",
                "Map.size(filed(List.map(.currency, List.filter(f -> f.amount > 0,"
                        + " List.flatMap(d -> d.forecasts, ds)))))")) {
            JsonNode line = only(differentCounts(reportOf(ACROSS.formatted(count + " == 1"))));
            assertEquals(ACROSS_OF_EACH_ELEMENT,
                    line.at("/lineId/target/quantity/counted").asString(), count);
        }
        JsonNode line = only(differentCounts(reportOf(ACROSS.formatted(
                "Map.size(Map.filterEntries((_, n) -> n > 0,"
                        + " totalsOf(List.flatMap(d -> d.forecasts, ds)))) == 1"))));
        assertEquals(ACROSS_OF_EACH_VALUE, line.at("/lineId/target/quantity/counted").asString());
    }

    /**
     * A value two lists hold is one value: a currency in two desks is counted once, whichever
     * desk holds which of its forecasts, and not once for each desk.
     */
    @Test
    void aValueTwoOfTheListsHoldIsCountedOnce() {
        String kept = "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0,"
                + " List.flatMap(d -> d.forecasts, ds))))) == 1";
        JsonNode once = only(differentCounts(reportOf(ACROSS.formatted(kept) + """
                example f
                    | "one currency in two desks" : ([
                        Desk { forecasts = [Forecast { currency = "USD", amount = 10 }] },
                        Desk { forecasts = [Forecast { currency = "USD", amount = 20 },
                            Forecast { currency = "EUR", amount = -5 }] }]) -> 1
                """)));
        assertTrue(pointAt(once, "on").path("hit").asBoolean(), once::toString);

        JsonNode two = only(differentCounts(reportOf(ACROSS.formatted(kept) + """
                example f
                    | "two currencies, one in each desk" : ([
                        Desk { forecasts = [Forecast { currency = "USD", amount = 10 }] },
                        Desk { forecasts = [Forecast { currency = "EUR", amount = 20 }] }]) -> 0
                """)));
        assertFalse(pointAt(two, "on").path("hit").asBoolean(), two::toString);
        assertTrue(pointsAt(two, "off").stream().anyMatch(off -> off.path("hit").asBoolean()
                && "2".equals(off.path("against").asString())), two::toString);
    }

    /**
     * Asked of what the elements under a value come to, they are those of every list: {@code 10}
     * in one desk and {@code -10} in another total nought, and keep nothing.
     */
    @Test
    void aValueIsCountedWhereWhatItsElementsInEveryListComeToMeetsTheStatement() {
        JsonNode cancelled = only(differentCounts(reportOf(ACROSS.formatted(
                "Map.size(Map.filterEntries((_, n) -> n > 0,"
                        + " totalsOf(List.flatMap(d -> d.forecasts, ds)))) == 1") + """
                example f
                    | "one above nought in each of two desks" : ([
                        Desk { forecasts = [Forecast { currency = "USD", amount = 10 }] },
                        Desk { forecasts = [Forecast { currency = "USD", amount = -10 }] }]) -> 0
                """)));
        assertFalse(pointAt(cancelled, "on").path("hit").asBoolean(), cancelled::toString);
        assertTrue(pointsAt(cancelled, "off").stream().anyMatch(off -> off.path("hit").asBoolean()
                && "0".equals(off.path("against").asString())), cancelled::toString);
    }

    /**
     * The rows composed for a line on the values across the lists share the elements out over
     * them, and answer as their points say: two forecasts of one currency meeting the statement
     * two ways, on either side of five, the forecasts under one currency totalling a number, and
     * a total of a hundred and fifty where no forecast in any desk is above a hundred.
     */
    @Test
    void everyRowComposedAcrossTheListsAnswersAsItsPointSays() {
        String desk = DECLARED + "data Desk = { forecasts: List<Forecast> }\n\n";
        everyRowComposedAnswersAsItsPointSays(desk + """
                behavior f : (ds: List<Desk>) -> Int
                let f (ds) = if Set.size(Set.fromList(List.map(.currency,
                    List.filter(f -> f.amount > 0 && f.amount /= 5,
                        List.flatMap(d -> d.forecasts, ds))))) == 2 then 1 else 0
                """, "f/#different ds [ds[*].forecasts[*].currency] where"
                + " [ds[*].forecasts[*].amount /= 5 && ds[*].forecasts[*].amount > 0]");
        for (String total : List.of("n > 0", "n == 0")) {
            everyRowComposedAnswersAsItsPointSays(desk + """
                    behavior f : (ds: List<Desk>) -> Int
                    let f (ds) = if Map.size(Map.filterEntries((_, n) -> %s,
                        totalsOf(List.flatMap(d -> d.forecasts, ds)))) == 1 then 1 else 0
                    """.formatted(total), "f/#different ds [ds[*].forecasts[*].currency] where"
                    + " [total(ds[*].forecasts[*].amount by currency) "
                    + total.substring("n ".length()) + "]");
        }
        everyRowComposedAnswersAsItsPointSays(desk + """
                behavior f : (ds: List<Desk>) -> Int
                let f (ds) = if List.all(d -> List.all(f -> f.amount <= 100, d.forecasts), ds)
                    then if Map.size(Map.filterEntries((_, n) -> n == 150,
                        totalsOf(List.flatMap(d -> d.forecasts, ds)))) == 1 then 1 else 0
                    else 2
                """, "f/#different ds [ds[*].forecasts[*].currency] where"
                + " [total(ds[*].forecasts[*].amount by currency) == 150]");
    }

    /**
     * What keeps an element may read the list holding it, and then it turns on which list each
     * element is put in, as it does when it reads the element holding the list.
     */
    @Test
    void aStatementReadingTheListHoldingTheElementHasNoRowsChosenAcrossThem() {
        JsonNode line = only(differentCounts(reportOf(ACROSS.formatted(
                "Set.size(Set.fromList(List.map(.currency, List.flatMap(d ->"
                        + " List.filter(f -> f.amount > List.length(d.forecasts), d.forecasts),"
                        + " ds)))) == 1"))));
        for (JsonNode item : line.path("items")) {
            assertFalse(item.path("knownWritable").asBoolean(), item::toString);
        }
    }

    /** Forecasts with a region, kept by it on the way to the count. */
    private static final String REGIONED = """
            module probe

            data Forecast = { currency: String, amount: Int, region: String }
            data Desk = { forecasts: List<Forecast> }

            let totalsOf (fs: List<Forecast>): Map<String, Int> =
                List.fold((acc, f) -> Map.updateOrInsert(f.currency, f.amount,
                    n -> n + f.amount, acc), Map.empty, fs)

            """;

    /**
     * Two filters on the way are one statement, both of them: one above the other, over one list
     * or over the lists a flattening puts end to end, or one above the flattening and one inside
     * its closure — and a fold gathering the values reads them as the law does.
     */
    @Test
    void twoFiltersOnTheWayAreOneStatementOfBoth() {
        String direct = REGIONED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if %s == 1 then 1 else 0
                """;
        String across = REGIONED + """
                behavior f : (ds: List<Desk>) -> Int
                let f (ds) = if %s == 1 then 1 else 0
                """;
        for (String count : List.of(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0,"
                        + " List.filter(f -> f.region == \"EU\", fs)))))",
                "Set.size(List.fold((acc, f) -> Set.insert(f.currency, acc), Set.empty,"
                        + " List.filter(f -> f.amount > 0, List.filter(f -> f.region == \"EU\","
                        + " fs))))")) {
            JsonNode line = only(differentCounts(reportOf(direct.formatted(count))));
            assertEquals("#different fs [fs[*].currency] where [fs[*].amount > 0"
                    + " && fs[*].region == EU]",
                    line.at("/lineId/target/quantity/counted").asString(), count);
        }
        for (String count : List.of(
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0,"
                        + " List.filter(f -> f.region == \"EU\","
                        + " List.flatMap(d -> d.forecasts, ds))))))",
                "Set.size(Set.fromList(List.map(.currency, List.filter(f -> f.amount > 0,"
                        + " List.flatMap(d -> List.filter(f -> f.region == \"EU\", d.forecasts),"
                        + " ds)))))")) {
            JsonNode line = only(differentCounts(reportOf(across.formatted(count))));
            assertEquals("#different ds [ds[*].forecasts[*].currency] where"
                    + " [ds[*].forecasts[*].amount > 0 && ds[*].forecasts[*].region == EU]",
                    line.at("/lineId/target/quantity/counted").asString(), count);
        }
    }

    /**
     * An element the closure of a flattening kept is an element of the list inside the outer
     * element, and a statement about it reads that element's places — not the outer element's,
     * which holds no such field.
     */
    @Test
    void aStatementAboutAnElementAFlatteningsClosureKeptReadsThatElement() {
        JsonNode behavior = behaviorOf(reportOf(REGIONED + """
                behavior f : (ds: List<Desk>) -> Int
                let f (ds) = if List.any(f -> f.amount > 0, List.flatMap(d ->
                    List.filter(g -> g.region == "EU", d.forecasts), ds)) then 1 else 0
                """));
        List<String> axes = new ArrayList<>();
        behavior.at("/partition/boundaries").forEach(each -> axes.add(each.path("axis")
                .asString()));
        assertTrue(axes.contains("f/ds[*].forecasts[*].amount"), axes::toString);
        List<String> read = new ArrayList<>();
        behavior.at("/partition/notRead").forEach(each -> read.add(each.path("position")
                .asString()));
        assertFalse(read.contains("ds[*].amount"), read::toString);
    }

    /**
     * Where a filter kept some elements before a fold filed them under their keys, a key is
     * counted where some kept element holds it and what the kept ones under it total meets the
     * statement: the elements of other regions add nothing to the total, and a currency only they
     * hold is no entry. Over one list and over the lists a flattening puts end to end.
     */
    @Test
    void theEntriesOfWhatAFilterKeptAreTheValuesItKeptWhoseTotalMeetsTheStatement() {
        String direct = REGIONED + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Map.size(Map.filterEntries((_, n) -> n > 0,
                    totalsOf(List.filter(f -> f.region == "EU", fs)))) == 1 then 1 else 0
                """;
        String kept = "#different fs [fs[*].currency] where [total(fs[*].amount kept by fs"
                + " meeting Ordered[term=fs[*].region, at=EU, proposition=EQ] by currency) > 0"
                + " && fs[*].region == EU]";
        JsonNode line = only(differentCounts(reportOf(direct + """
                example f
                    | "one EU currency above nought" : ([
                        Forecast { currency = "USD", amount = 10, region = "EU" },
                        Forecast { currency = "USD", amount = -20, region = "US" },
                        Forecast { currency = "JPY", amount = 5, region = "US" }]) -> 1
                """)));
        assertEquals(kept, line.at("/lineId/target/quantity/counted").asString());
        assertTrue(pointAt(line, "on").path("hit").asBoolean(), line::toString);
        everyRowComposedAnswersAsItsPointSays(direct.substring("module probe\n\n".length()),
                "f/" + kept);

        JsonNode across = only(differentCounts(reportOf(REGIONED + """
                behavior f : (ds: List<Desk>) -> Int
                let f (ds) = if Map.size(Map.filterEntries((_, n) -> n > 0,
                    totalsOf(List.filter(f -> f.region == "EU",
                        List.flatMap(d -> d.forecasts, ds))))) == 1 then 1 else 0
                """)));
        assertEquals("#different ds [ds[*].forecasts[*].currency] where"
                + " [total(ds[*].forecasts[*].amount kept by ds[*].forecasts meeting"
                + " Ordered[term=ds[*].forecasts[*].region, at=EU, proposition=EQ] by currency)"
                + " > 0 && ds[*].forecasts[*].region == EU]",
                across.at("/lineId/target/quantity/counted").asString());
    }

    /** Movements filed under the field each case of them names its stock by. */
    private static final String MOVEMENTS = """
            data Receipt = { sku: String, quantity: Int }
            data Issue = { sku: String, quantity: Int }
            data Stocktake = { sku: String, counted: Int }
            data Movement = Receipt | Issue | Stocktake

            let summed (ms: List<Movement>): Map<String, Int> =
                List.fold((acc, m) -> match m with
                        | Receipt { sku, quantity } ->
                            Map.updateOrInsert(sku, quantity, on -> on + quantity, acc)
                        | Issue { sku, quantity } ->
                            Map.updateOrInsert(sku, 0 - quantity, on -> on - quantity, acc)
                        | Stocktake { sku, counted } ->
                            Map.updateOrInsert(sku, counted, on -> on + counted, acc),
                    Map.empty, ms)

            let onHand (ms: List<Movement>): Map<String, Int> =
                List.fold((acc, m) -> match m with
                        | Receipt { sku, quantity } ->
                            Map.updateOrInsert(sku, quantity, on -> on + quantity, acc)
                        | Issue { sku, quantity } ->
                            Map.updateOrInsert(sku, 0 - quantity, on -> on - quantity, acc)
                        | Stocktake { sku, counted } -> Map.insert(sku, counted, acc),
                    Map.empty, ms)

            behavior f : (ms: List<Movement>) -> Int
            """;

    /** The value a movement is filed under, the field its case names. */
    private static final String SKU = "when ms[*]@Receipt[sum-case] then"
            + " ms[*]@Receipt[sum-case].sku when ms[*]@Issue[sum-case] then"
            + " ms[*]@Issue[sum-case].sku when ms[*]@Stocktake[sum-case] then"
            + " ms[*]@Stocktake[sum-case].sku";

    /**
     * A fold filing each element under the field its case names is a count of the different
     * values those fields hold: a receipt and a stocktake of one sku are one entry. Its entries a
     * statement keeps are the values whose total meets it — added up over every case, or from the
     * last stocktake put — and a row at each point of the line answers as its point says.
     */
    @Test
    void theEntriesOfAFoldFilingEachCaseUnderAFieldOfItsOwnAreCountedByTheValue() {
        String summed = "module probe\n\n" + MOVEMENTS + """
                let f (ms) = if Map.size(Map.filterEntries((_, on) -> on > 0, summed(ms))) == 1
                    then 1 else 0
                """;
        JsonNode once = only(differentCounts(reportOf(summed + """
                example f
                    | "a receipt and a stocktake of one sku" : ([
                        Receipt { sku = "A", quantity = 5 },
                        Stocktake { sku = "A", counted = 3 }]) -> 1
                    | "two skus" : ([Receipt { sku = "A", quantity = 5 },
                        Stocktake { sku = "B", counted = 3 }]) -> 0
                """)));
        assertTrue(once.at("/lineId/target/quantity/counted").asString()
                .startsWith("#different ms [" + SKU + "] where [total("), once::toString);
        assertTrue(pointAt(once, "on").path("hit").asBoolean(), once::toString);
        assertTrue(pointsAt(once, "off").stream().anyMatch(off -> off.path("hit").asBoolean()
                && "2".equals(off.path("against").asString())), once::toString);
        everyRowComposedAnswersAsItsPointSays(summed.substring("module probe\n\n".length()),
                "f/" + once.at("/lineId/target/quantity/counted").asString());

        String onHand = "module probe\n\n" + MOVEMENTS + """
                let f (ms) = if Map.size(Map.filterEntries((_, on) -> on > 0, onHand(ms))) == 1
                    then 1 else 0
                """;
        // A stocktake puts what it counted in place of what was on hand: counted last, nought is
        // what the sku has.
        JsonNode put = only(differentCounts(reportOf(onHand + """
                example f
                    | "a receipt, then nothing counted" : ([
                        Receipt { sku = "A", quantity = 5 },
                        Stocktake { sku = "A", counted = 0 }]) -> 0
                    | "nothing counted, then a receipt" : ([
                        Stocktake { sku = "A", counted = 0 },
                        Receipt { sku = "A", quantity = 5 }]) -> 1
                """)));
        assertTrue(pointAt(put, "on").path("hit").asBoolean(), put::toString);
        assertTrue(pointsAt(put, "off").stream().anyMatch(off -> off.path("hit").asBoolean()
                && "0".equals(off.path("against").asString())), put::toString);
        everyRowComposedAnswersAsItsPointSays(onHand.substring("module probe\n\n".length()),
                "f/" + put.at("/lineId/target/quantity/counted").asString());
    }

    /**
     * A line on what the kept elements under a key total has rows composed for it: each element
     * written inside what keeps it — a number away from five, a region held at one text — so
     * every element written is kept and the total is theirs.
     */
    @Test
    void aLineOnWhatTheKeptElementsUnderAKeyTotalHasRowsComposedForIt() {
        String declared = REGIONED.substring("module probe\n\n".length());
        everyRowComposedAnswersAsItsPointSays(declared + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Map.size(Map.filterEntries((_, n) -> n > 0,
                    totalsOf(List.filter(f -> f.amount /= 5, fs)))) >= 1 then 1 else 0
                """, "f/total(fs[*].amount kept by fs meeting !Affine[form=LinearForm["
                + "constant=-5, coefs={fs[*].amount=1}], proposition=EQ] by currency)");
        everyRowComposedAnswersAsItsPointSays(declared + """
                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if Map.size(Map.filterEntries((_, n) -> n > 0,
                    totalsOf(List.filter(f -> f.region == "EU", fs)))) >= 1 then 1 else 0
                """, "f/total(fs[*].amount kept by fs meeting Ordered[term=fs[*].region, at=EU,"
                + " proposition=EQ] by currency)");
    }

    /**
     * What keeps an element may read the element of the outer list holding its list, and then it
     * turns on which list each element is put in: no row is composed by choosing the elements as
     * one container, and none is said to be.
     */
    @Test
    void aStatementReadingTheElementHoldingTheListHasNoRowsChosenAcrossThem() {
        JsonNode line = only(differentCounts(reportOf("module probe\n\n" + DECLARED + """
                data Desk = { floor: Int, forecasts: List<Forecast> }

                behavior f : (ds: List<Desk>) -> Int
                let f (ds) = if Set.size(Set.fromList(List.map(.currency, List.flatMap(d ->
                    List.filter(f -> f.amount > d.floor, d.forecasts), ds)))) == 1 then 1 else 0
                """)));
        assertEquals("#different ds [ds[*].forecasts[*].currency] where"
                        + " [ds[*].floor - ds[*].forecasts[*].amount < 0]",
                line.at("/lineId/target/quantity/counted").asString());
        for (JsonNode item : line.path("items")) {
            assertFalse(item.path("knownWritable").asBoolean(), item::toString);
        }
    }

    /**
     * A row this compiler composes for a point of a line answers what the point says, as the
     * language runs it: the rows of a line on {@code compared}, the last condition before the
     * answer is written, are each written as an example answering one above the line and nought
     * below it, and none of them is refused.
     *
     * <p>The rows themselves, and not examples written beside them: what a row is composed holding
     * is what is asked of it here, and a row the composer could not have built is never one an
     * example stands in for.
     *
     * @param behavior   a behavior {@code f} answering one where {@code compared} holds and nought
     *                   where it fails, under whatever conditions it is reached — of some element,
     *                   where it is a number of each
     * @param outOfReach the points of the line no row reaches, by where each is, which are said to
     *                   have no row and never to have one composed
     */
    private static void everyRowComposedAnswersAsItsPointSays(String behavior, String compared,
                                                              String... outOfReach) {
        String source = "module probe\n\n" + behavior;
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        // Rendered at their places in the source, so the origin of one comparison is none of
        // another's.
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation).json(rendering));
        JsonNode drawn = null;
        for (JsonNode each : behaviorOf(report).at("/partition/boundaries")) {
            if (compared.equals(each.path("axis").asString())) {
                drawn = each;
            }
        }
        assertTrue(drawn != null, () -> "a line on " + compared + ": " + report);
        for (JsonNode item : drawn.path("items")) {
            if (List.of(outOfReach).contains(item.path("against").asString())) {
                assertFalse(item.path("knownWritable").asBoolean(),
                        () -> "no row reaches " + item + ", and none is said to");
                continue;
            }
            assertTrue(item.has("notOwed") || item.path("knownWritable").asBoolean(),
                    () -> "a row is composed for every point of " + compared + ": " + item);
        }
        String origin = drawn.path("origin").asString();
        String rows = GeneratedRows.of(compilation, "probe", null, rendering).text();
        StringBuilder examples = new StringBuilder("\nexample f\n");
        List<String> said = new ArrayList<>();
        StringBuilder row = null;
        int written = 0;
        for (String line : rows.split("\n")) {
            if (line.startsWith("// fills ")) {
                said.add(line);
                continue;
            }
            if (line.startsWith("    |")) {
                row = new StringBuilder();
            }
            if (row == null) {
                continue;
            }
            row.append(line).append('\n');
            if (!line.contains("<?>")) {
                continue;
            }
            // A number of each element puts one row at a point for each element: the row is above
            // the line where some element is.
            String answer = null;
            for (String fills : said) {
                if (fills.endsWith(" point of " + origin)) {
                    answer = fills.contains("fills ON ") || fills.contains("fills IN ")
                            || "1".equals(answer) ? "1" : "0";
                }
            }
            if (answer != null) {
                examples.append(row.toString().replace("<?>", answer));
                written++;
            }
            said.clear();
            row = null;
        }
        assertTrue(written > 0, () -> "rows composed for " + compared + ": " + rows);
        Compilation run = Compilation.ofSource(source + examples, "Main");
        run.measure(Adequacy.Asked.fullReport());
        run.answerEverything();
        assertEquals(List.of(), run.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                () -> "every row of " + compared + " answers as its point says:" + examples
                        + "\nout of the rows composed:\n" + rows);
    }

    private static JsonNode reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "every example answers what it writes");
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    private static JsonNode behaviorOf(JsonNode report) {
        for (JsonNode each : report.at("/modules/0/behaviors")) {
            if ("f".equals(each.path("name").asString())) {
                return each;
            }
        }
        throw new AssertionError("a behavior f in " + report);
    }

    private static List<JsonNode> differentCounts(JsonNode report) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, out);
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("items")
                && "count_of_different_values".equals(node.path("kind").asString())) {
            out.add(node);
        }
        node.forEach(child -> collect(child, out));
    }

    private static JsonNode only(List<JsonNode> lines) {
        assertEquals(1, lines.size(), () -> "one line on the count: " + lines);
        return lines.getFirst();
    }

    private static JsonNode pointAt(JsonNode line, String point) {
        return pointsAt(line, point).getFirst();
    }

    private static List<JsonNode> pointsAt(JsonNode line, String point) {
        List<JsonNode> out = new ArrayList<>();
        line.path("items").forEach(each -> {
            if (point.equals(each.path("point").asString())) {
                out.add(each);
            }
        });
        if (out.isEmpty()) {
            throw new AssertionError("a " + point + " point on " + line);
        }
        return out;
    }
}
