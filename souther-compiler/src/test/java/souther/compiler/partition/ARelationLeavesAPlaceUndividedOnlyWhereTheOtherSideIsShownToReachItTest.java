package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation between two values is said to leave a place undivided only where the other side is
 * shown to stand at every value the relation needs it at, beside every value the place may hold.
 *
 * <p>Each model below is one relation, and what is asked is the word the report gives each place
 * it relates. Three things are shown apart and none of them stands in for another: that the other
 * side takes every value of a run (an unrestricted value, or a number taken of one whose operation
 * declares every number it could answer is one some value answers), that its run is every value
 * between the ends and not only where the values lie, and that nothing on the way to the relation
 * ties it to another place.
 */
class ARelationLeavesAPlaceUndividedOnlyWhereTheOtherSideIsShownToReachItTest {

    private static final String RELATES = "relates";

    private static final String NOT_SHOWN = "not shown";

    /** The word each place is left with by the comparison at {@code at}, by its name. */
    private static Map<String, String> left(String inputs, String declarations, String body,
                                            String at) {
        Compilation compilation = Compilation.ofSource("""
                module w1
                %s
                behavior m : (%s) -> Bool
                let m (%s) = %s
                """.formatted(declarations, inputs, inputs.replaceAll(": [A-Za-z]+", ""), body),
                "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        Map<String, String> out = new LinkedHashMap<>();
        for (String line : report.lines().map(String::strip).toList()) {
            if (!line.contains("comparison@" + at + " ") || !line.contains("about `")) {
                continue;
            }
            if (!line.startsWith("· no line") && !line.startsWith("· not read")) {
                continue;
            }
            String place = line.substring(line.lastIndexOf("about `") + 7, line.length() - 1);
            out.put(place, line.contains("rather than dividing the values here") ? RELATES
                    : line.contains("not shown to reach every value here") ? NOT_SHOWN : line);
        }
        return out;
    }

    @Test
    void aValueHeldToARunReachesWhatLiesInItAndNoMore() {
        assertEquals(Map.of("a", RELATES, "n", NOT_SHOWN),
                left("a: Amount, n: Int", "data Amount = Int invariant value >= 0",
                        "n == a.value", "4:18"));
    }

    @Test
    void aLengthReachesEveryNumberAtOrAboveNoughtAndNothingBelow() {
        assertEquals(Map.of("String.length(s)", RELATES, "n", NOT_SHOWN),
                left("n: Int, s: String", "data Unused = Int", "n == String.length(s)", "4:18"));
        assertEquals(Map.of("n", RELATES, "String.length(s)", NOT_SHOWN),
                left("n: N, s: String", "data N = Int invariant value >= 0",
                        "n.value == String.length(s)", "4:24"));
    }

    /** A string held to two values takes two lengths with a gap between them. */
    @Test
    void aLengthOfAStringARuleHoldsReachesNothingShown() {
        assertEquals(Map.of("String.length(s)", RELATES, "n", NOT_SHOWN),
                left("n: Int, s: S", "data S = String invariant value == \"a\" || value == \"aaa\"",
                        "n == String.length(s.value)", "4:18"));
    }

    /** An hour is one of twenty-four, which a number running past them is not. */
    @Test
    void anHourReachesTheHoursOfADay() {
        assertEquals(Map.of("Time.hour(t)", RELATES, "n", NOT_SHOWN),
                left("n: Int, t: Time", "data Unused = Int", "n == Time.hour(t)", "4:18"));
        assertEquals(Map.of("h", RELATES, "Time.hour(t)", NOT_SHOWN),
                left("h: H, t: Time", "data H = Int invariant value >= 0 && value <= 23",
                        "h.value == Time.hour(t)", "4:24"));
    }

    /** The years a date can be written in stop somewhere, and a number past them is one no date
     *  is in; and a date held to two first days of January is in two years with one between. */
    @Test
    void aYearReachesTheYearsADateCanBeWrittenInAndNoGapARuleLeaves() {
        assertEquals(Map.of("Date.year(d)", RELATES, "y", NOT_SHOWN),
                left("y: Int, d: Date", "data Unused = Int", "y == Date.year(d)", "4:18"));
        assertEquals(Map.of("y", RELATES, "Date.year(d)", NOT_SHOWN),
                left("y: Y, d: Date", "data Y = Int invariant value >= 1 && value <= 9999",
                        "y.value == Date.year(d)", "4:24"));
        assertEquals(Map.of("Date.year(d)", RELATES, "y", NOT_SHOWN),
                left("y: Int, d: D", "data D = Date invariant value == Date(\"2020-01-01\")"
                        + " || value == Date(\"2022-01-01\")", "y == Date.year(d.value)", "4:18"));
    }

    /**
     * A day apart, the last date has no date after it and the first none before; that is where the
     * dates stop and no line the model draws. Moved together, two dates are a day apart wherever
     * they stand, and only how far apart they are settles it. A date and a count of days are not
     * moved together.
     */
    @Test
    void twoValuesADayApartRelateEachOther() {
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Date, b: Date", "data Unused = Int", "Date.daysBetween(a, b) == 1",
                        "4:39"));
        assertEquals(Map.of("a", NOT_SHOWN, "n", NOT_SHOWN),
                left("a: Date, n: Int", "data Unused = Int",
                        "Date.daysBetween(Date(\"2026-01-01\"), a) <= n", "4:56"));
    }

    /**
     * The last case of an enumeration, the empty string and the last second of a day are values a
     * model holds, and a relation that comes out one way only there divides them: {@code a < b} is
     * false at the last stage whatever {@code b} is, and at the empty {@code b} whatever {@code a}
     * is. No string is the greatest, so every {@code a} has strings either side. The ends of an
     * {@code Int} are where the representation stops, and two of them relate each other; so do two
     * stages held equal, since every stage has one equal to it and one not.
     */
    @Test
    void anEndAModelHoldsIsAValueTheRelationDivides() {
        String stage = "data Stage = Prospecting | Negotiation | Won | Lost";
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Stage, b: Stage", stage, "a < b", "4:18"));
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Stage, b: Stage", stage, "if a <= b then a < b else false", "4:33"));
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Stage, b: Stage", stage, "a == b", "4:18"));
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN),
                left("a: String, b: String", stage, "a < b", "4:18"));
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Time, b: Time", stage, "a < b", "4:18"));
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Int, b: Int", stage, "a < b", "4:18"));
    }

    /**
     * No two dates are ten trillion days apart, so the comparison holds for none of them; and
     * four hundred billion days apart are only dates nearer the two ends than the middle is.
     * Three hundred billion days leave the middle date partners either side.
     */
    @Test
    void aDifferenceHasToBeOneTheMiddleOfTheTypeReachesBothWays() {
        for (String apart : List.of("10000000000000", "400000000000")) {
            assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                    left("a: Date, b: Date", "data Unused = Int",
                            "Date.daysBetween(a, b) > " + apart, "4:39"), apart);
        }
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Date, b: Date", "data Unused = Int",
                        "Date.daysBetween(a, b) > 300000000000", "4:39"));
    }

    /**
     * A rule between two stages of a record is measured to the end: a row for it is composed by
     * moving one stage by how far apart the rule leaves the two, and a move past the last stage is
     * a run reaching as far as the stages do, or no run, never a place with nothing at it.
     */
    @Test
    void aRuleBetweenTwoStagesIsMeasuredToTheEnd() {
        Compilation compilation = Compilation.ofSource("""
                module w1
                data Stage = Prospecting | Negotiation | Won | Lost
                data Deal = { from: Stage, to: Stage }
                    invariant from < to
                behavior m : (d: Deal) -> Bool
                let m (d) = true
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        for (String place : List.of("d.from", "d.to")) {
            assertTrue(report.lines().anyMatch(line -> line.contains("invariant Deal #1")
                    && line.contains("not shown to reach every value here")
                    && line.endsWith("about `" + place + "`")), report);
        }
    }

    /**
     * The model the question was asked with: how many days are left before a deadline, held at
     * nought or more and then at fourteen or less. Both comparisons are about how far apart the
     * two dates are, so neither date is divided by either and what is measured is the two borders
     * on the difference.
     */
    @Test
    void howManyDaysAreLeftBeforeADeadlineDividesNeitherDate() {
        Compilation compilation = Compilation.ofSource("""
                module check

                data TooLate = { days: Int }
                data TooEarly = { days: Int }
                data Fine = { days: Int }

                behavior check : (deadline: Date, today: Date) -> Fine | TooLate | TooEarly

                let check (deadline, today) = {
                    let left = Date.daysBetween(today, deadline)
                    guard left >= 0 else TooLate { days = left }
                    guard left <= 14 else TooEarly { days = left }
                    Fine { days = left }
                }

                example check
                    | (Date("2026-08-01"), Date("2026-07-25")) -> Fine { days = 7 }
                    | (Date("2026-07-20"), Date("2026-07-25")) -> TooLate { days = -5 }
                    | (Date("2026-09-01"), Date("2026-07-25")) -> TooEarly { days = 38 }
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("measurement: complete"), report);
        assertFalse(report.contains("not shown to reach every value here"), report);
        for (String place : List.of("deadline", "today")) {
            assertEquals(2, report.lines().filter(line -> line.contains("· no line: comparison@")
                    && line.contains("rather than dividing the values here")
                    && line.endsWith("about `" + place + "`")).count(), report);
        }
    }

    /**
     * A guard on how far apart two dates are leaves them moved together: at nought or more, the
     * difference is at fourteen or less and past it. A guard on one of them alone keeps it from
     * values of its own, and a guard holding the difference to ten or less leaves it never past
     * fourteen.
     */
    @Test
    void aGuardOnHowFarApartTwoValuesAreLeavesThemMovedTogether() {
        String apart = "Date.daysBetween(a, b)";
        assertEquals(Map.of("a", RELATES, "b", RELATES),
                left("a: Date, b: Date", "data Unused = Int",
                        "if " + apart + " >= 0 then " + apart + " <= 14 else false", "4:75"));
        assertEquals(Map.of("a", NOT_SHOWN, "b", NOT_SHOWN),
                left("a: Date, b: Date", "data Unused = Int",
                        "if a >= Date(\"2020-01-01\") then " + apart + " <= 14 else false",
                        "4:71"));
        Map<String, String> under = left("a: Date, b: Date", "data Unused = Int",
                "if " + apart + " <= 10 then " + apart + " <= 14 else false", "4:76");
        assertEquals(Set.of("a", "b"), under.keySet());
        assertFalse(under.containsValue(RELATES), under.toString());
    }

    @Test
    void twoValuesOfOneDeclaredTypeReachEachOther() {
        assertEquals(Map.of("c", RELATES, "e", RELATES),
                left("c: Code, e: Code",
                        "data Code = String invariant String.matches(\"[A-Z]{2}\", value)",
                        "e.value == c.value", "4:24"));
    }

    /**
     * A guard on one place narrows where it runs and ties it to nothing: the other place still
     * reaches it. What it reaches is the narrowed run, which a value of the other place below it
     * is not on.
     */
    @Test
    void aGuardOnOnePlaceNarrowsItAndTiesItToNothing() {
        assertEquals(Map.of("a", RELATES, "b", NOT_SHOWN),
                left("a: Int, b: Int", "data Unused = Int", "if a > 0 then a < b else false",
                        "4:32"));
    }

    /**
     * What a weighed term has to stand at is the rest over its weight: under {@code 2h + y < 0}
     * with {@code y} at most minus five, {@code y} at minus five needs an {@code h} below two and a
     * half, which an {@code h} from four on never is.
     */
    @Test
    void aWeighedTermHasToStandAtTheRestOverItsWeight() {
        String declarations = "data Y = Int invariant value >= -10 && value <= -5";
        assertEquals(Map.of("h", NOT_SHOWN, "y", NOT_SHOWN),
                left("h: Int, y: Y", declarations,
                        "if h >= 4 && h <= 11 then 2 * h + y.value < 0 else false", "4:58"));
        assertEquals(Map.of("h", NOT_SHOWN, "y", RELATES),
                left("h: Int, y: Y", declarations,
                        "if h >= 0 && h <= 20 then 2 * h + y.value < 0 else false", "4:58"));
    }

    /**
     * A way that chooses is proved along each choice: under {@code x == 0 || x == 1} a row holds
     * {@code x} at nought or at one, so a {@code y} of two makes {@code x == y} false wherever the
     * row arrives, though the two choices together leave {@code x} anything a whole number can be
     * between them.
     */
    @Test
    void aWayThatChoosesIsProvedAlongEachChoice() {
        assertEquals(Map.of("x", RELATES, "y", NOT_SHOWN),
                left("x: Int, y: Int", "data Unused = Int",
                        "if x == 0 || x == 1 then x == y else false", "4:43"));
    }

    /**
     * Two choices on places apart are proved along every way of taking them together, and not
     * along each alternative once: {@code y} reaches every {@code x} along three of the four, and
     * along the last — {@code x} from twenty, {@code y} up to ten — it reaches none.
     */
    @Test
    void choicesOnPlacesApartAreProvedAlongEveryWayOfTakingThemTogether() {
        assertEquals(Map.of("x", NOT_SHOWN, "y", NOT_SHOWN),
                left("x: Int, y: Int", "data Unused = Int",
                        "if (x >= 0 && x <= 10 || x >= 20 && x <= 30)"
                                + " && (y >= 0 && y <= 30 || y >= 0 && y <= 10)"
                                + " then x == y else false", "4:112"));
    }

    /**
     * A run whose end the rules put at a third is handed over from a hair below it, which no
     * value of {@code x} is, so it is not taken as a run {@code x} fills — here, where the values
     * asked of it are all above a third, as anywhere. An end at a half is written as it is.
     */
    @Test
    void anEndRoundedPastTheRulesIsNotTakenAsOneTheTermReaches() {
        String declarations = "data Y = Decimal invariant value >= 0.6m && value <= 0.9m";
        assertEquals(Map.of("x", NOT_SHOWN, "y", NOT_SHOWN),
                left("x: Decimal, y: Y", declarations,
                        "if x + x + x >= 1m && x <= 1m then x == y.value else false", "4:53"));
        assertEquals(Map.of("x", NOT_SHOWN, "y", RELATES),
                left("x: Decimal, y: Y", declarations,
                        "if x + x >= 1m && x <= 1m then x == y.value else false", "4:49"));
    }

    /** An end a run of dense values does not take is no value asked of where every value asked of
     *  is inside it: between nought and one, {@code x} is at every value from a fifth to a half. */
    @Test
    void anEndADenseRunDoesNotTakeIsNoGapInsideIt() {
        assertEquals(Map.of("x", NOT_SHOWN, "y", RELATES),
                left("x: Decimal, y: Y", "data Y = Decimal invariant value >= 0.2m && value <= 0.5m",
                        "if x > 0m && x < 1m then x == y.value else false", "4:43"));
    }

    /** A way over the sum of two places ties them, however each runs on its own: moved together,
     *  the two are no longer as far from nought as they were. */
    @Test
    void aWayOverTwoPlacesTiesThem() {
        assertEquals(Map.of("x", NOT_SHOWN, "y", NOT_SHOWN),
                left("x: Int, y: Int", "data Unused = Int",
                        "if x + y <= 1 then x == y else false", "4:37"));
    }

    /** A way over another number of the date a year is taken of ties the year to it: a date on
     *  the twenty-ninth of February is in a leap year. */
    @Test
    void aWayOverAnotherNumberOfTheSamePlaceTiesTheNumberTakenOfIt() {
        assertEquals(List.of(NOT_SHOWN), List.copyOf(left("y: Int, d: Date", "data Unused = Int",
                "if Date.month(d) == 2 && Date.day(d) == 29 then y == Date.year(d) else false",
                "4:66").entrySet().stream()
                .filter(each -> each.getKey().equals("y")).map(Map.Entry::getValue).toList()));
    }

    private static final String EMPLOYEE = "data EmpId = String invariant String.length(value) >= 1";

    /** A rule of the record over two of its other fields holds back neither the field compared
     *  nor anything beside it, however many such rules there are and however they are written. */
    @Test
    void aRuleOfTheRecordOverItsOtherFieldsTiesTheFieldComparedToNothing() {
        Map<String, String> reached = Map.of("approver", RELATES, "p.boss", RELATES);
        for (String rules : List.of("", "invariant low <= high",
                "invariant low <= high && high >= low", "invariant ordered(low, high)")) {
            assertEquals(reached, left("p: Pending, approver: EmpId", EMPLOYEE
                    + "\nlet ordered (a: Int, b: Int): Bool = a <= b"
                    + "\ndata Pending = { me: EmpId, boss: EmpId, low: Int, high: Int } " + rules,
                    "approver == p.boss", "6:32"), rules);
        }
    }

    /** Rows that cover the comparison still satisfy the model once the record carries a rule over
     *  two of its other fields. */
    @Test
    void rowsCoveringTheComparisonSatisfyAModelWhoseRecordRulesOverItsOtherFields() {
        Compilation compilation = Compilation.ofSource("""
                module eqrepro

                data EmpId = String
                    invariant String.length(value) >= 1

                data Pending = { me: EmpId, boss: EmpId, low: Int, high: Int }
                    invariant low <= high
                data Granted
                data Denied

                behavior approve : (p: Pending, approver: EmpId) -> Granted | Denied

                let approve (p, approver) = {
                    guard approver == p.boss else Denied
                    Granted
                }

                example approve
                    | "boss" : (Pending { me = EmpId("a"), boss = EmpId("b"), low = 1, high = 2 }, EmpId("b")) -> Granted
                    | "other" : (Pending { me = EmpId("a"), boss = EmpId("b"), low = 1, high = 2 }, EmpId("c")) -> Denied
                    | "equal bounds" : (Pending { me = EmpId("xx"), boss = EmpId("x"), low = 0, high = 0 }, EmpId("x")) -> Granted
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors(), "the rows hold");
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /** A rule of the record that names the field compared may hold it back, whether it ties it to
     *  another field or bounds it alone. */
    @Test
    void aRuleOfTheRecordNamingTheFieldComparedIsNotShownToLeaveItReachingEveryValue() {
        for (String rule : List.of("invariant boss == me",
                "invariant String.length(boss.value) >= 2")) {
            assertEquals(Map.of("approver", NOT_SHOWN, "p.boss", NOT_SHOWN),
                    left("p: Pending, approver: EmpId", EMPLOYEE
                            + "\ndata Pending = { me: EmpId, boss: EmpId } " + rule,
                            "approver == p.boss", "5:32"), rule);
        }
    }

    /**
     * A rule of a value two out reads places, not fields: a record's rule over
     * {@code pending.low} and a newtype's over {@code value.low} read beside {@code boss}, and the
     * same rules over {@code boss} read it.
     */
    @Test
    void aRuleFurtherOutReadsThePlacesItNamesAndNotTheFieldTheyStartAt() {
        String pending = EMPLOYEE + "\ndata Pending = { me: EmpId, boss: EmpId, low: Int, high: Int }";
        assertEquals(Map.of("approver", RELATES, "e.pending.boss", RELATES),
                left("e: Envelope, approver: EmpId", pending
                        + "\ndata Envelope = { pending: Pending } invariant pending.low <= pending.high",
                        "approver == e.pending.boss", "6:32"));
        assertEquals(Map.of("approver", NOT_SHOWN, "e.pending.boss", NOT_SHOWN),
                left("e: Envelope, approver: EmpId", pending
                        + "\ndata Envelope = { pending: Pending } invariant pending.boss == pending.me",
                        "approver == e.pending.boss", "6:32"));
        assertEquals(Map.of("approver", RELATES, "p.boss", RELATES),
                left("p: WrappedPending, approver: EmpId", pending
                        + "\ndata WrappedPending = Pending invariant value.low <= value.high",
                        "approver == p.value.boss", "6:32"));
        assertEquals(Map.of("approver", NOT_SHOWN, "p.boss", NOT_SHOWN),
                left("p: WrappedPending, approver: EmpId", pending
                        + "\ndata WrappedPending = Pending invariant value.boss == value.me",
                        "approver == p.value.boss", "6:32"));
    }

    /** How many a set holds, read down a chain of fields from a newtype wrapping a record. */
    @Test
    void aRuleOverHowManyASetFurtherDownHoldsBackNoElement() {
        assertEquals(Map.of("champ", RELATES, "w.members[*]", RELATES), left("champ: EmpId, w: Wrapped",
                EMPLOYEE + "\ndata Inner = { members: Set<EmpId> }"
                        + "\ndata Wrapped = Inner invariant Set.size(value.members) >= 1",
                "Set.contains(champ, w.value.members)", "6:20"));
    }

    /** How many a set holds is shown of the count, however little the rules of the record it
     *  sits in are shown of the rest: a pattern a field beside it is held to, which no range
     *  states, says nothing of the count. */
    @Test
    void aSetsCountIsShownOfItselfBesideAFieldWhoseRuleNoRangeStates() {
        assertEquals(Map.of("champ", RELATES, "o.makers[*]", RELATES), left("champ: EmpId, o: Opp",
                EMPLOYEE + "\ndata Ds = Set<EmpId> invariant Set.size(value) >= 1"
                        + "\ndata Code = String invariant String.matches(\"[A-Z]{2}\", value)"
                        + "\ndata Opp = { code: Code, makers: Ds }",
                "Set.contains(champ, o.makers.value)", "7:20"));
    }

    /** A rule of a record a field sits in, two records out, over another of its fields. */
    @Test
    void aRuleOfARecordFurtherOutOverAnotherOfItsFieldsTiesTheFieldComparedToNothing() {
        assertEquals(Map.of("approver", RELATES, "o.p.boss", RELATES),
                left("o: Outer, approver: EmpId", EMPLOYEE
                        + "\ndata Pending = { me: EmpId, boss: EmpId }"
                        + "\ndata Outer = { p: Pending, n: Int } invariant n >= 0",
                        "approver == o.p.boss", "6:32"));
    }

    /** How many a set holds says nothing of which values its elements take, so long as it may
     *  hold one; held to none, its elements are values it never holds. */
    @Test
    void aRuleOverHowManyASetHoldsHoldsBackNoElementUnlessItHoldsNone() {
        assertEquals(Map.of("champ", RELATES, "ds[*]", RELATES), left("champ: EmpId, ds: Ds",
                EMPLOYEE + "\ndata Ds = Set<EmpId> invariant Set.size(value) >= 1",
                "Set.contains(champ, ds.value)", "5:21"));
        assertEquals(Map.of("champ", RELATES, "ds.members[*]", RELATES), left("champ: EmpId, ds: Ds",
                EMPLOYEE + "\ndata Ds = { members: Set<EmpId> } invariant Set.size(members) >= 1",
                "Set.contains(champ, ds.members)", "5:21"));
        assertEquals(NOT_SHOWN, left("champ: EmpId, ds: Ds",
                EMPLOYEE + "\ndata Ds = Set<EmpId> invariant Set.size(value) <= 0",
                "Set.contains(champ, ds.value)", "5:21").get("champ"));
    }

    /** Held to more than one, a set's elements are that many values apart, which is a question
     *  of the element's type this does not ask: not shown, though a type of strings has them. */
    @Test
    void aSetHeldToMoreThanOneIsNotShownToLeaveItsElementsEveryValue() {
        assertEquals(NOT_SHOWN, left("champ: EmpId, ds: Ds",
                EMPLOYEE + "\ndata Ds = Set<EmpId> invariant Set.size(value) == 2",
                "Set.contains(champ, ds.value)", "5:21").get("champ"));
    }
}
