package souther.compiler;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where every run getting to a rule stops in an operation past where the representation of a
 * number stops, on the values of one place an input holds, the report says the invariant that
 * keeps every run from there: on the data holding the place, on the side the run stops past, and
 * as far out as it can be. The value itself is the domain's, so what is said is that bound, and
 * declaring it takes the stop away.
 *
 * <p>A parameter no data holds is bounded in a data of its type the author introduces for it.
 *
 * <p>Not where a run stops where the clauses of a type a construction makes leave the number,
 * which the model already states and its own words are about; nor where it stops on a sum of two
 * inputs, which no bound on either alone keeps it from.
 */
class AnInvariantIsSuggestedWhereARunStopsAtARepresentationsEndTest {

    /** What the reading says, rows not looked for: the suggestion is said of the reading. */
    private static final Adequacy.Asked READ = new Adequacy.Asked(Adequacy.Level.OFF, false);

    private static String report(String source) {
        Compilation compilation = ACompiledModel.measured(source, READ);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<String> suggested(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("· declaring `invariant ")).toList();
    }

    private static final String ABOVE = """
            module m

            data P = { x: Int }%s

            behavior f : (p: P) -> Bool
            let f (p) = p.x + 10 > 0
            """;

    @Test
    void aSumPastTheGreatestIntIsKeptFromByAnUpperBoundOnTheField() {
        String report = report(ABOVE.formatted(""));

        assertEquals(List.of("· declaring `invariant x <= 9223372036854775797` on P keeps every"
                + " run from stopping there; a bound one step further out lets in a run that stops"
                + " there, and the value to declare is the one the domain has"), suggested(report),
                report);
    }

    /** Declared, the run stops nowhere, and nothing is suggested. */
    @Test
    void theBoundDeclaredTakesTheStopAway() {
        String report = report(ABOVE.formatted("\n    invariant x <= 9223372036854775797"));

        assertFalse(report.contains("may stop a run"), report);
        assertFalse(report.contains("stop not resolved"), report);
        assertEquals(List.of(), suggested(report), report);
    }

    private static final String A_DAY_BACK = """
            module m

            data P = { birthday: Date }%s

            behavior f : (p: P) -> Bool
            let f (p) = Date.addDays(0 - 1, p.birthday) > Date("2000-01-01")
            """;

    /** A date is a value of the input a stop is shown at: the first day there is, which the day
     *  before is past, so the bound is as far out as it can be. */
    @Test
    void aDateMovedPastTheFirstDayIsKeptFromByALowerBoundOnTheField() {
        String report = report(A_DAY_BACK.formatted(""));

        assertEquals(List.of("· declaring `invariant birthday >= Date(\"-999999999-01-02\")` on P"
                + " keeps every run from stopping there; a bound one step further out lets in a run"
                + " that stops there, and the value to declare is the one the domain has"),
                suggested(report), report);
    }

    @Test
    void theBoundOnTheDateDeclaredTakesTheStopAway() {
        String report = report(A_DAY_BACK.formatted(
                "\n    invariant birthday >= Date(\"-999999999-01-02\")"));

        assertFalse(report.contains("may stop a run"), report);
        assertFalse(report.contains("stop not resolved"), report);
        assertEquals(List.of(), suggested(report), report);
    }

    /** The year of a date shifted by days is a number of the date it is shifted from, which a run
     *  works out only where the shifts get there. */
    private static final String THE_YEAR_OF_A_SHIFT = """
            module m

            data P = { birthday: Date }%s

            behavior f : (p: P, on: Date) -> Bool
            let f (p, on) = Date.year(on) - Date.year(%s) >= 60
            """;

    @Test
    void aShiftTakenThroughAYearIsKeptFromByALowerBoundOnTheField() {
        String report = report(THE_YEAR_OF_A_SHIFT.formatted("",
                "Date.addDays(0 - 1, p.birthday)"));

        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant birthday >= Date(\"-999999999-01-02\")` on P"), report);
    }

    /** Shifts that move by nothing together stop where one of them is past the calendar. */
    @Test
    void shiftsThatMoveByNothingStopAtTheFirstDayAllTheSame() {
        String report = report(THE_YEAR_OF_A_SHIFT.formatted("",
                "Date.addDays(1, Date.addDays(0 - 1, p.birthday))"));

        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant birthday >= Date(\"-999999999-01-02\")` on P"), report);
    }

    @Test
    void theBoundOnTheShiftedDateDeclaredTakesTheStopAway() {
        String report = report(THE_YEAR_OF_A_SHIFT.formatted(
                "\n    invariant birthday >= Date(\"-999999999-01-02\")",
                "Date.addDays(0 - 1, p.birthday)"));

        assertFalse(report.contains("may stop a run"), report);
    }

    /** A date moved by months inside what the comparison holds aside stops where the month it
     *  lands in is past the calendar, which is a run of the dates it moves. */
    private static final String MOVED_BY_MONTHS = """
            module m

            data P = { on: Date }%s

            behavior f : (p: P) -> Bool
            let f (p) =
                Int.floorMod(Date.daysBetween(Date("2000-01-02"), Date.addMonths(%s, p.on)), 7) >= 1
            """;

    @Test
    void aDateMovedPastTheLastMonthIsKeptFromByTheLastDayOfTheMonthBefore() {
        String report = report(MOVED_BY_MONTHS.formatted("", "1"));

        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant on <= Date(\"+999999999-11-30\")` on P"), report);
    }

    @Test
    void aDateMovedBeforeTheFirstMonthIsKeptFromByTheFirstDayOfTheMonthAfter() {
        String report = report(MOVED_BY_MONTHS.formatted("", "0 - 1"));

        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant on >= Date(\"-999999999-02-01\")` on P"), report);
    }

    @Test
    void theBoundOnTheMonthDeclaredTakesTheStopAway() {
        String report = report(MOVED_BY_MONTHS.formatted(
                "\n    invariant on <= Date(\"+999999999-11-30\")", "1"));

        assertFalse(report.contains("may stop a run"), report);
        assertFalse(report.contains("· not read:"), report);
    }

    /** Days moved back off the first of a month and forward again move it by nothing, and the
     *  move back stops all the same where that first day is the calendar's: the stop is said. */
    @Test
    void aMoveOffTheFirstOfAMonthUndoneStopsWhereTheMoveBackDoes() {
        String report = report("""
                module m

                data P = { on: Date }

                let monthStart (d: Date): Date = Date.addDays(1 - Date.day(d), d)

                behavior f : (p: P) -> Bool
                let f (p) = Int.floorMod(Date.daysBetween(Date("2000-01-02"),
                    Date.addDays(1, Date.addDays(0 - 1, monthStart(p.on)))), 7) >= 1
                """);

        assertTrue(report.lines().map(String::strip).anyMatch(line ->
                (line.startsWith("· may stop a run:") || line.startsWith("· stop not resolved:"))
                        && line.contains("-Date.day(p.on) + p.on")), report);
    }

    /** A value chosen by cases is worked out on each arm a run takes: the bound is the arm's that
     *  stops nearest, where the comparison is the behavior's answer as where it is a condition. */
    @Test
    void aValueChosenByCasesIsBoundedByTheArmThatStopsNearest() {
        String report = report(ON_AN_ARM.replace("Int\nlet f (i) = if ", "Bool\nlet f (i) = ")
                .replace(" then 1 else 2", ""));

        assertEquals(List.of("· declaring `invariant issuedOn <= Date(\"+999999999-11-30\")` on"
                + " Invoice keeps every run from stopping there; a bound one step further out lets"
                + " in a run that stops there, and the value to declare is the one the domain has"),
                suggested(report), report);
    }

    /** How far out a bound goes is asked of the region: with the other bound held, no run past
     *  either takes the arm that stops there, and neither is said to be as far out as it can be. */
    @Test
    void howFarOutABoundGoesIsAskedWithEveryOtherBoundHeld() {
        String report = report("""
                module m

                data P = { x: Int, y: Int }

                behavior f : (p: P) -> Int
                let f (p) =
                    if (if p.x == 9223372036854775807 then p.y + 1 else p.x + 1) > 0 then 1 else 0
                """);

        assertEquals(2, suggested(report).size(), report);
        assertTrue(suggested(report).stream()
                .noneMatch(line -> line.contains("one step further out")), report);
    }

    /** A rule read at two calls says one region, and where one call leaves its stop with no bound
     *  said, no bound said keeps every run of the rule going. */
    @Test
    void aRuleReadWhereOneCallHasNoBoundSaysNone() {
        String report = report("""
                module m

                data P = { x: Int, y: Int }

                let h (a: Int): Bool = a + 1 > 0

                behavior f : (p: P) -> Bool
                let f (p) = h(p.x) && h(p.x - p.y)
                """);

        assertTrue(report.contains("· may stop a run"), report);
        assertEquals(List.of(), suggested(report), report);
    }

    /** A rule read at two calls that bound one place differently says the tighter bound, once:
     *  the looser keeps no run of the other call going. */
    @Test
    void aRuleReadAtTwoCallsSaysTheTighterBoundOnce() {
        String report = report("""
                module m

                data P = { x: Int }

                let h (a: Int): Bool = a + 1 > 0

                behavior f : (p: P) -> Bool
                let f (p) = h(p.x) && h(p.x + 1)
                """);

        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant x <= 9223372036854775805` on P"), report);
    }

    /** Stated as a condition, the arm a run takes is put on the way: a value of the input is shown
     *  to take the arm and stop there, and the bound is as far out as it can be by that run. */
    private static final String ON_AN_ARM = """
            module m

            data Terms = Net15 | Net30

            data Invoice = { terms: Terms, issuedOn: Date }

            let nominal (i: Invoice): Date =
                match i.terms with
                    | Net15 -> Date.addDays(15, i.issuedOn)
                    | Net30 -> Date.addDays(30, i.issuedOn)

            behavior f : (i: Invoice) -> Int
            let f (i) = if Date.addDays(1, nominal(i)) > Date("2000-01-01") then 1 else 2
            """;

    @Test
    void aRunTakingTheArmThatStopsNearestIsShownAndSetsTheBound() {
        String report = report(ON_AN_ARM);

        assertTrue(report.contains("· may stop a run:"), report);
        assertEquals(List.of("· declaring `invariant issuedOn <= Date(\"+999999999-11-30\")` on"
                + " Invoice keeps every run from stopping there; a bound one step further out lets"
                + " in a run that stops there, and the value to declare is the one the domain has"),
                suggested(report), report);
    }

    /** A walk makes every element of a list before a search looks at any: the element no row
     *  gets to the search with is made by every run all the same, and bounds the input. */
    @Test
    void anElementASearchNeverGetsToIsMadeByEveryRunAllTheSame() {
        String report = report("""
                module m

                import List ( map, find, rangeInclusive )

                behavior f : (s: Date, from: Date) -> Date
                let f (s, from) =
                    rangeInclusive(0, 2)
                        |> map(n -> Date.addDays(n, from))
                        |> find(d -> Int.floorMod(Date.daysBetween(s, d), 7) >= 1)
                        |> Option.withDefault(from)
                """);

        assertEquals(List.of("· no data holds `from`, whose type is `Date`: introducing a data of"
                + " `Date` that declares `invariant value <= Date(\"+999999999-12-29\")`"),
                introduced(report).stream().map(line -> line.substring(0, line.indexOf(", and")))
                        .toList(), report);
    }

    /** Days moved off the first of a month, one move over another and in an arm of a choice, stop
     *  where that first day moved by all of them is past the calendar. */
    @Test
    void daysMovedOffTheFirstOfAMonthInAnArmStopWhereTheMonthIsPastTheCalendar() {
        String report = report("""
                module m

                data T = A | B

                data P = { on: Date, t: T }

                let monthStart (d: Date): Date = Date.addDays(1 - Date.day(d), d)

                let nominal (p: P): Date =
                    match p.t with
                        | A -> Date.addDays(2, Date.addDays(0 - 1,
                                Date.addMonths(1, monthStart(p.on))))
                        | B -> p.on

                behavior f : (s: Date, p: P) -> Bool
                let f (s, p) = Int.floorMod(Date.daysBetween(s, nominal(p)), 7) >= 1
                """);

        assertFalse(report.contains("· not read:"), report);
        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant on <= Date(\"+999999999-11-30\")` on P"), report);
    }

    /** A place whose own type is written under a name is bounded in that type, as its value. */
    @Test
    void aPlaceOfANamedTypeIsBoundedInThatType() {
        String report = report("""
                module m

                data Day = Int

                behavior f : (d: Day) -> Bool
                let f (d) = d.value + 1 > 0
                """);

        assertEquals(1, suggested(report).size(), report);
        assertTrue(suggested(report).getFirst().startsWith(
                "· declaring `invariant value <= 9223372036854775806` on Day"), report);
    }

    @Test
    void aSumOfTwoInputsIsKeptFromByNoBoundOnEither() {
        String report = report("""
                module m

                data P = { x: Int, y: Int }

                behavior f : (p: P) -> Bool
                let f (p) = p.x + p.y > 0
                """);

        assertTrue(report.contains("may stop a run"), report);
        assertEquals(List.of(), suggested(report), report);
    }

    /** A parameter no data holds is bounded in a data the author introduces for it, of its
     *  type, as that data's value. */
    @Test
    void aParameterNoDataHoldsIsBoundedInADataIntroducedForIt() {
        String report = report(A_PARAMETER);

        assertEquals(List.of("· no data holds `x`, whose type is `Int`: introducing a data of"
                + " `Int` that declares `invariant value <= 9223372036854775797`, and taking `x`"
                + " as it, keeps every run from stopping there; a bound one step further out lets"
                + " in a run that stops there, and the value to declare is the one the domain has"),
                introduced(report), report);
    }

    /** The document says the same: the parameter and its type in place of a data, and the
     *  clause on the data's value, in a document the schema takes. */
    @Test
    void theDocumentNamesTheParameterAndItsTypeInPlaceOfAData() {
        Compilation compilation = ACompiledModel.measured(A_PARAMETER, READ);
        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<JsonNode> keeping = document.findValues("keeping");

        assertEquals(1, keeping.size(), document::toString);
        assertEquals(1, keeping.getFirst().size(), document::toString);
        JsonNode bound = keeping.getFirst().get(0);
        assertEquals(Set.of("parameter", "type", "invariant", "furthestOut"),
                Set.copyOf(bound.propertyNames()), document::toString);
        assertEquals("x", bound.get("parameter").asString());
        assertEquals("Int", bound.get("type").asString());
        assertEquals("invariant value <= 9223372036854775797", bound.get("invariant").asString());
        assertTrue(bound.get("furthestOut").asBoolean(), document::toString);
        EveryObjectThisWritesIsShapedTheWayTheSchemaSaysTest.assertShapedLikeTheSchema(document);
    }

    private static final String A_PARAMETER = """
            module m

            behavior f : (x: Int) -> Bool
            let f (x) = x + 10 > 0
            """;

    private static List<String> introduced(String report) {
        return report.lines().map(String::strip)
                .filter(line -> line.startsWith("· no data holds ")).toList();
    }

    /** A construction stops a run where the clauses of the type it makes leave the number, which
     *  the model states: the report's words on it are its own, and no bound is suggested. */
    @Test
    void aStopWhereAConstructionsClausesLeaveTheNumberIsGivenNoBound() {
        String report = report("""
                module m

                data Count = Int
                    invariant value >= 0

                data P = { n: Int }

                behavior f : (p: P) -> Bool
                let f (p) = Count(p.n).value > 3
                """);

        assertTrue(report.contains("may stop a run"), report);
        assertEquals(List.of(), suggested(report), report);
    }
}
