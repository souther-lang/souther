package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;
import org.opentest4j.AssertionFailedError;

import souther.compiler.DocumentShape;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.BinaryOperator;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A map a fold builds by filing what each element holds under its key, keeping the lesser or the
 * greater of that and what was filed before, holds under a key the least or the greatest of what
 * the elements of that key hold — so a statement about one of its values is a statement about
 * that end of the key's values, and a row is composed on each side of it.
 *
 * <p>Not a statement about what any one element holds. Of two elements of one key holding four and
 * ten, the least is four, and an element holding at least seven says nothing of whether the least
 * is: a line read off the elements' own values would put a row at the wrong side of it.
 */
class AFoldThatKeepsOneEndOfWhatEachKeyFilesAnswersThatEndOfItsValuesTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String LEAST =
            "Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, t.days), acc)";

    private static final String GREATEST =
            "Map.updateOrInsert(t.account, t.days, seen -> Int.max(seen, t.days), acc)";

    /** One touch of an account. */
    private record Touch(String account, int days) {

        String written() {
            return "Touch { account = \"" + account + "\", days = " + days + " }";
        }
    }

    /** One row offered for {@code stale}: the touches and the threshold. */
    private record Row(List<Touch> touches, int staleAfter) {

        /** What the fold files under each account, keeping {@code end} of two values. */
        Map<String, Integer> filed(BinaryOperator<Integer> end) {
            Map<String, Integer> out = new LinkedHashMap<>();
            for (Touch each : touches) {
                out.merge(each.account(), each.days(), end);
            }
            return out;
        }

        /** The entries the filter keeps. */
        Map<String, Integer> kept(BinaryOperator<Integer> end) {
            Map<String, Integer> out = new LinkedHashMap<>();
            filed(end).forEach((account, days) -> {
                if (days >= staleAfter) {
                    out.put(account, days);
                }
            });
            return out;
        }

        /** The row as the language writes its inputs. */
        String written() {
            return touches.stream().map(Touch::written).toList() + ", " + staleAfter;
        }
    }

    private static String modelOf(String step, String more) {
        return """
                module example.stale

                data Touch = { account: String, days: Int }

                let sinceOf (touches: List<Touch>): Map<String, Int> =
                    List.fold((acc, t) -> %s, Map.empty, touches)

                behavior stale : (touches: List<Touch>, staleAfter: Int) -> Map<String, Int>

                let stale (touches, staleAfter) =
                    Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches))
                %s""".formatted(step, more);
    }

    @Test
    void aLineOnTheLeastOfAKeysValuesIsOwedOfferedAndThenMet() {
        String examples = """

                example stale
                    | "none" : ([], 2) -> []
                """;
        Compilation before = measured(modelOf(LEAST, examples));
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), unmetOf(before),
                () -> "every point of the line is owed: " + report(before));
        assertTrue(json(before).contains("least(touches[*].days by account)"),
                () -> "the line is on the least of a key's values: " + report(before));

        List<Row> offered = offeredRows(before);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));
        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Row row : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(row.written()).append(") -> ")
                    .append(entries(row.kept(Math::min))).append("\n");
        }
        Compilation after = measured(modelOf(LEAST, written.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /**
     * Two elements of one key holding four and ten, against ten: the least of them is six short of
     * the line, though one of them stands on it. So the row is no row at the line, and is one well
     * short of it.
     */
    @Test
    void theLeastOfAKeyAndNotAValueOfItIsWhatTheLineIsOn() {
        Compilation compilation = measured(modelOf(LEAST, """

                example stale
                    | "four and ten" : ([%s, %s], 10) -> []
                """.formatted(new Touch("a", 4).written(), new Touch("a", 10).written())));
        List<String> unmet = unmetOf(compilation);
        assertTrue(unmet.contains("ON"), () -> "the least is not on the line: " + unmet);
        assertFalse(unmet.contains("OUT"), () -> "it is well short of it: " + unmet);
    }

    /** And the same two read for the greatest: ten, which is on the line. */
    @Test
    void theGreatestOfAKeyIsWhatTheLineIsOnForAFoldKeepingTheGreater() {
        Compilation compilation = measured(modelOf(GREATEST, """

                example stale
                    | "four and ten" : ([%s, %s], 10) -> [("a", 10)]
                """.formatted(new Touch("a", 4).written(), new Touch("a", 10).written())));
        assertTrue(json(compilation).contains("greatest(touches[*].days by account)"),
                () -> report(compilation));
        List<String> unmet = unmetOf(compilation);
        assertFalse(unmet.contains("ON"), () -> "the greatest is on the line: " + unmet);
        assertTrue(unmet.contains("OUT"), () -> "and nothing is well short of it: " + unmet);
    }

    /** Elements of another key are no part of the end of this one's values. */
    @Test
    void anotherKeysValuesAreNotTakenIntoTheEnd() {
        Compilation compilation = measured(modelOf(LEAST, """

                example stale
                    | "apart" : ([%s, %s], 10) -> [("a", 10)]
                """.formatted(new Touch("a", 10).written(), new Touch("b", 4).written())));
        List<String> unmet = unmetOf(compilation);
        assertFalse(unmet.contains("ON"), () -> "a's least is ten, on the line: " + unmet);
        assertFalse(unmet.contains("OUT"), () -> "b's least is four, well short: " + unmet);
    }

    /** Which order the elements of a key come in is no part of which end of them is kept. */
    @Test
    void theOrderOfAKeysElementsDoesNotMoveTheEnd() {
        for (List<Touch> touches : List.of(
                List.of(new Touch("a", 4), new Touch("a", 10)),
                List.of(new Touch("a", 10), new Touch("a", 4)))) {
            Compilation compilation = measured(modelOf(LEAST, """

                    example stale
                        | "two" : (%s, 4) -> [("a", 4)]
                    """.formatted(touches.stream().map(Touch::written).toList())));
            assertFalse(unmetOf(compilation).contains("ON"),
                    () -> "the least is four whichever comes first: " + touches);
        }
    }

    /** An empty list files nothing, so no entry stands at any point of the line. */
    @Test
    void anEmptyListIsNoEntryForTheLineToHoldAt() {
        Compilation compilation = measured(modelOf(LEAST, """

                example stale
                    | "none" : ([], 2) -> []
                """));
        bordersOf(compilation).forEach(border -> border.path("items").forEach(item ->
                assertFalse(item.path("hit").asBoolean(),
                        () -> "no point of the line is where nothing is filed: " + item)));
    }

    /** The end kept, written with its two values the other way round, as an {@code if}, under a
     *  name given what the step answers, or as a lookup and a filing, is the same end. */
    @Test
    void theSameEndWrittenAnotherWayIsTheSameLine() {
        List<String> plain = axisOf(read(modelOf(LEAST, "")));
        for (String step : List.of(
                "Map.updateOrInsert(t.account, t.days, seen -> Int.min(t.days, seen), acc)",
                "Map.updateOrInsert(t.account, t.days,"
                        + " seen -> if t.days < seen then t.days else seen, acc)",
                "{ let next = Map.updateOrInsert(t.account, t.days,"
                        + " seen -> Int.min(seen, t.days), acc)  next }",
                "Map.updateOrInsert(t.account, t.days,"
                        + " seen -> { let d = t.days  Int.min(seen, d) }, acc)",
                "Map.updateOrInsert(t.account, t.days,"
                        + " seen -> { let kept = Int.min(seen, t.days)  kept }, acc)",
                """
                match Map.get(t.account, acc) with
                        | None -> Map.insert(t.account, t.days, acc)
                        | Some seen -> Map.insert(t.account, Int.min(seen, t.days), acc)""")) {
            Compilation compilation = read(modelOf(step, ""));
            assertEquals(plain, axisOf(compilation), () -> step + ": " + report(compilation));
        }
    }

    /**
     * The model the line was first missed in, as it was written: the map kept to its keys and
     * handed back inside a record. The comparison is read, and its line is on the least of a key's
     * values against the threshold. The least settles it whatever the threshold is only at the
     * greatest {@code Int}, where the threshold's type stops, so it is read. A container holding
     * one touch has the least of its key for that touch's days, so the least is shown every value
     * the days take, and the threshold every value of its type: nothing is left unread.
     */
    @Test
    void theStaleAccountsModelReadsItsComparison() {
        Compilation compilation = read("""
                module example.stale

                data Touch = { account: String, days: Int }

                data Report = { stale: List<String> }

                behavior staleAccounts : (touches: List<Touch>, staleAfter: Int) -> Report

                let staleAccounts (touches, staleAfter) = {
                    let since: Map<String, Int> =
                        List.fold((acc, t) -> Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, t.days), acc),
                                  Map.empty, touches)
                    Report { stale = Map.keys(Map.filterEntries((k, days) -> days >= staleAfter, since)) }
                }
                """);
        assertEquals(List.of(), report(compilation).lines()
                .filter(line -> line.contains("not read")).toList(), () -> report(compilation));
        assertEquals(1, bordersOf(compilation).size(), () -> report(compilation));
        assertTrue(json(compilation).contains("least(touches[*].days by account)"),
                () -> report(compilation));
    }

    /**
     * Touches a map took out of visits, one for each, keep the same ends under the same keys as the
     * visits do with the touch taken inside the step: the line is on the end of a place of the
     * visits, the rows offered are the rows a fold over the visits is offered, and written they
     * meet the line.
     */
    @Test
    void touchesAMapTookOutOfTheVisitsKeepTheEndsTheVisitsDo() {
        String examples = """

                example stale
                    | "none" : ([], 2) -> []
                """;
        String model = """
                module example.stale

                data Touch = { account: String, days: Int }

                data Visit = { touch: Touch, note: String }

                let sinceOf (visits: List<Visit>): Map<String, Int> =
                    List.fold((acc, t) -> %s, Map.empty, %s)

                behavior stale : (visits: List<Visit>, staleAfter: Int) -> Map<String, Int>

                let stale (visits, staleAfter) =
                    Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(visits))
                """;
        String projectedFold = model.formatted(LEAST,
                "List.reverse(List.map(v -> v.touch, visits))");
        Compilation direct = measured(model.formatted(
                "Map.updateOrInsert(t.touch.account, t.touch.days,"
                        + " seen -> Int.min(seen, t.touch.days), acc)", "visits") + examples);
        Compilation projected = measured(projectedFold + examples);
        assertTrue(json(projected).contains("least(visits[*].touch.days by touch.account)"),
                () -> report(projected));
        assertEquals(axisOf(direct), axisOf(projected), () -> report(projected));
        List<Offered> offered = offered(projected);
        assertFalse(offered.isEmpty(), () -> report(projected));
        assertEquals(offeredInputs(direct), offeredInputs(projected));

        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (Offered each : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(each.written()).append(") -> ")
                    .append(entries(each.row().kept(Math::min))).append("\n");
        }
        Compilation after = measured(projectedFold + written);
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    private static final String OVER_WHAT_A_MAP_BUILT = """
            module example.stale

            data Touch = { account: String, days: Int, on: Date }

            data Seen = { who: String, since: Int }

            let sinceOf (touches: List<Touch>, today: Date): Map<String, Int> =
                List.fold((acc, p) -> %s, Map.empty, %s)

            behavior stale : (touches: List<Touch>, today: Date, staleAfter: Int)
                -> Map<String, Int>

            let stale (touches, today, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches, today))
            """;

    /**
     * A tuple or a record a map built of each touch, either inside the other or a tuple inside a
     * tuple, with the key and the value read out of it, keeps the ends the touches do: the line is
     * the one a fold over the touches draws, and the rows offered are the ones it is offered.
     */
    @Test
    void aTupleOrARecordAMapBuiltOfTheTouchesKeepsTheEndsTheTouchesDo() {
        record Built(String step, String walked) { }
        Compilation direct = measured(OVER_WHAT_A_MAP_BUILT.formatted(
                "Map.updateOrInsert(p.account, p.days, seen -> Int.min(seen, p.days), acc)",
                "touches"));
        for (Built each : List.of(
                new Built("{ let (a, d) = p\n Map.updateOrInsert(a, d,"
                        + " seen -> Int.min(seen, d), acc) }",
                        "List.map(t -> (t.account, t.days), touches)"),
                new Built("Map.updateOrInsert(p.who, p.since,"
                        + " seen -> Int.min(seen, p.since), acc)",
                        "List.map(t -> Seen { who = t.account, since = t.days }, touches)"),
                new Built("{ let (q, d) = p\n let (a, _) = q\n Map.updateOrInsert(a, d,"
                        + " seen -> Int.min(seen, d), acc) }",
                        "List.map(t -> ((t.account, 0), t.days), touches)"),
                new Built("{ let (s, _) = p\n Map.updateOrInsert(s.who, s.since,"
                        + " seen -> Int.min(seen, s.since), acc) }",
                        "List.map(t -> (Seen { who = t.account, since = t.days }, 0), touches)"))) {
            Compilation built = measured(OVER_WHAT_A_MAP_BUILT.formatted(each.step(),
                    each.walked()));
            assertTrue(json(built).contains("least(touches[*].days by account)"),
                    () -> each + ": " + report(built));
            assertEquals(axisOf(direct), axisOf(built), () -> each + ": " + report(built));
            assertEquals(offeredInputs(direct), offeredInputs(built), () -> each.toString());
        }
    }

    /**
     * A value worked out of what an element holds, alone or with another input, is the end of that
     * value, read as a fold over the touches writing it of each touch reads it. Where it is a
     * multiple of one place and a number, the end is that multiple of the end of the place, turned
     * over where the multiple is negative: the least of {@code today - on} is {@code today} less
     * the greatest of {@code on}, and of {@code days + 1} the least of {@code days}, moved by one.
     */
    @Test
    void aValueWorkedOutOfWhatTheElementHoldsIsTheEndOfThatValue() {
        Map<String, String> endOfThePlace = Map.of(
                "t.days + 1", "least(touches[*].days by account)",
                "Date.daysBetween(t.on, today)", "greatest(touches[*].on by account)");
        for (Map.Entry<String, String> each : endOfThePlace.entrySet()) {
            String since = each.getKey();
            Compilation built = read(OVER_WHAT_A_MAP_BUILT.formatted(
                    "Map.updateOrInsert(p.who, p.since, seen -> Int.min(seen, p.since), acc)",
                    "List.map(t -> Seen { who = t.account, since = " + since + " }, touches)"));
            String direct = since.replace("t.", "p.");
            Compilation written = read(OVER_WHAT_A_MAP_BUILT.formatted(
                    "Map.updateOrInsert(p.account, " + direct + ", seen -> Int.min(seen, "
                            + direct + "), acc)", "touches"));
            assertEquals(List.of(each.getValue()), endsOf(built),
                    () -> since + ": " + report(built));
            assertEquals(endsOf(written), endsOf(built), () -> since + ": " + report(built));
        }
    }

    private static final String FILTERED = """
            module example.stale

            data Touch = { account: String, days: Int, on: Date }
                invariant days >= 0 && days <= 100

            let sinceOf (touches: List<Touch>, today: Date): Map<String, Int> =
                List.fold((acc, p) -> Map.updateOrInsert(p.account, %1$s,
                                                         seen -> Int.min(seen, %1$s), acc),
                          Map.empty, touches)

            behavior stale : (touches: List<Touch>, today: Date, staleAfter: Int)
                -> Map<String, Int>

            let stale (touches, today, staleAfter) =
                Map.filterEntries((_, days) -> days %2$s staleAfter, sinceOf(touches, today))
            """;

    /**
     * The end of a key's values, each a multiple of one place and a number, is that multiple of the
     * end of the place: the comparison of it with a threshold is read, the threshold is shown every
     * value, and the line is the plain one moved by the number.
     */
    @Test
    void theEndOfAShiftedPlaceIsReadAcrossAndItsLineIsMovedByTheShift() {
        String plain = report(measured(FILTERED.formatted("p.days", ">=")));
        String shifted = report(measured(FILTERED.formatted("p.days + 1", ">=")));
        assertEquals(List.of(), unreadAnywhere(plain), plain);
        // The line of the plain end is on the threshold being the end (the ON point) and one above
        // it (the OFF point): the shifted end is one more, so its line is one lower.
        String on = "least(touches[*].days by account) - staleAfter: = ";
        assertTrue(plain.contains(on + "0") && plain.contains(on + "-1"), plain);
        assertTrue(shifted.contains(on + "-1") && shifted.contains(on + "-2"), shifted);
        assertFalse(plain.contains(on + "-2") || shifted.contains(on + "0"), shifted);
        assertEquals(List.of(), unreadAbout("staleAfter", shifted), shifted);
    }

    private static final String BESIDE = """
            module example.stale

            data Touch = { account: String, days: Int }
                invariant days >= 0 && days <= 100

            let sinceOf (touches: List<Touch>, bonus: Int): Map<String, Int> =
                List.fold((acc, p) -> Map.updateOrInsert(p.account, %1$s,
                                                         seen -> %2$s(seen, %1$s), acc),
                          Map.empty, touches)

            behavior stale : (touches: List<Touch>, bonus: Int, staleAfter: Int)
                -> Map<String, Int>

            let stale (touches, bonus, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches, bonus))
            """;

    /** The relation of the end of a key with the threshold, as the report spells its form. */
    private static List<String> formsRead(String report) {
        return report.lines().filter(line -> line.contains("read as stale/")
                        && line.contains("staleAfter: "))
                .map(line -> line.substring(line.indexOf("read as stale/") + 14,
                        line.indexOf(": ")))
                .distinct().sorted().toList();
    }

    /**
     * What stands beside every element is the same for every element, so it is added to the end
     * once, whatever the element is weighed by: the least of {@code bonus - days} is {@code bonus}
     * less the greatest of {@code days}, and of {@code 2 * days + bonus} twice the least of
     * {@code days} with {@code bonus} added. The number beside is not multiplied with the element.
     */
    @Test
    void theNumberBesideIsAddedToTheEndOnceWhateverTheElementIsWeighedBy() {
        Map<String, List<String>> expected = Map.of(
                "Int.min|bonus - p.days", List.of(
                        "bonus - greatest(touches[*].days by account) - staleAfter"),
                "Int.min|p.days + bonus", List.of(
                        "bonus + least(touches[*].days by account) - staleAfter"),
                "Int.min|2 * p.days + bonus", List.of(
                        "bonus + 2 * least(touches[*].days by account) - staleAfter"),
                "Int.max|bonus - 2 * p.days", List.of(
                        "bonus - 2 * least(touches[*].days by account) - staleAfter"));
        Map<String, List<String>> read = new TreeMap<>();
        for (String key : expected.keySet()) {
            String[] how = key.split("\\|");
            read.put(key, formsRead(report(measured(BESIDE.formatted(how[1], how[0])))));
        }
        assertEquals(new TreeMap<>(expected), read);
    }

    /**
     * Of three numbers a relation asks about two, and what the way states of those two is held to
     * their difference: whichever of the three the other two are asked beside. A statement of the
     * second and the third is read when the first is the one held still, and not only a statement
     * of the first and the second.
     */
    @Test
    void whatTheWayStatesOfTheTwoAskedAboutIsHeldWhicheverOfThreeTheyAre() {
        // A statement of a and b is about their difference, and the relation weighs the two alike
        // and so asks of their sum: it is not read, which no choice of the pair changes.
        Map<String, String> unreadAbout = Map.of(
                "b >= c", "a",
                "a >= c", "b");
        for (Map.Entry<String, String> each : unreadAbout.entrySet()) {
            String source = """
                    module example.three

                    behavior f : (a: Int, b: Int, c: Int) -> Bool

                    let f (a, b, c) = %s && a + b - c >= 0
                    """.formatted(each.getKey());
            String report = report(read(source));
            List<String> unread = unreadAnywhere(report);
            // The number held still is settled at one end by the statement, which is why it is
            // the one that is not read: the other two are.
            assertEquals(1, unread.size(), each.getKey() + "\n" + report);
            assertTrue(unread.getFirst().endsWith("about `" + each.getValue() + "`"),
                    each.getKey() + "\n" + report);
        }
    }

    private static final String UNBOUNDED = """
            module example.stale

            data Touch = { account: String, days: Int }

            let sinceOf (touches: List<Touch>): Map<String, Int> =
                List.fold((acc, p) -> Map.updateOrInsert(p.account, %1$s,
                                                         seen -> Int.min(seen, %1$s), acc),
                          Map.empty, touches)

            behavior stale : (touches: List<Touch>, staleAfter: Int) -> Map<String, Int>

            let stale (touches, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches))
            """;

    /**
     * The end of a multiple of a place is the multiple of the end of the place, but the program
     * still works out the multiple of each element, and that stops a run at the greatest {@code
     * Int}: a value the arithmetic cannot hold is not one some row reaches. So the comparison is
     * not shown to get every value the end takes, and is read only where the elements' own numbers
     * are what is filed.
     */
    @Test
    void theEndOfAMultipleIsNotShownReachedWhereWorkingOutTheMultipleCanStopARun() {
        assertEquals(List.of(), unreadAnywhere(report(measured(UNBOUNDED.formatted("p.days")))));
        for (String since : List.of("p.days + 1", "p.days - 1", "2 * p.days", "0 - p.days")) {
            String report = report(measured(UNBOUNDED.formatted(since)));
            assertTrue(unreadAnywhere(report).stream()
                    .anyMatch(line -> line.contains("a run may stop")), since + "\n" + report);
        }
    }

    /**
     * Taken from a number, a place is turned over: the least of {@code today - on} is {@code today}
     * less the greatest of {@code on}. Read as the least of {@code on}, the line would be on the
     * wrong end of the dates.
     */
    @Test
    void theLeastOfWhatIsTakenAwayFromANumberIsTheGreatestOfThePlace() {
        Compilation compilation = measured(
                FILTERED.formatted("Date.daysBetween(p.on, today)", ">="));
        assertEquals(List.of(), unreadAnywhere(report(compilation)), report(compilation));
        assertEquals(List.of("greatest(touches[*].on by account)"), endsOf(compilation),
                () -> report(compilation));
    }

    /**
     * Twice a place takes the even values only: an equality of it with the threshold has no row
     * at an odd threshold, and the threshold is not shown every value however the end is read.
     */
    @Test
    void aMultipleOfAPlaceLeavesTheValuesBetweenItsMultiplesUnreached() {
        String equal = report(measured(FILTERED.formatted("2 * p.days", "==")));
        assertTrue(equal.contains("2 * least(touches[*].days by account)"), equal);
        assertFalse(unreadAbout("staleAfter", equal).isEmpty(), equal);
    }

    private static final String ALONE_IN_A_LIST = """
            module example.stale

            data Touch = { account: String, days: Int }
                %s

            data Quote = { touches: List<Touch> }
                %s

            let sinceOf (touches: List<Touch>): Map<String, Int> =
                List.fold((acc, p) -> Map.updateOrInsert(p.account, p.days,
                                                         seen -> Int.min(seen, p.days), acc),
                          Map.empty, touches)

            behavior stale : (quote: Quote, staleAfter: Int) -> Map<String, Int>

            let stale (quote, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(%s))
            """;

    /**
     * The end of a key is every value one touch takes where the list may hold one touch; where it
     * holds two at least, or keeps only some of its touches, one touch alone is not a row, and the
     * end is not shown to take every value.
     */
    @Test
    void theEndOfAKeyIsShownEveryValueOnlyWhereOneTouchAloneIsARow() {
        String bounded = "invariant days >= 0 && days <= 100";
        String two = "invariant List.length(touches) >= 2";
        String alone = report(measured(ALONE_IN_A_LIST.formatted(bounded, "", "quote.touches")));
        assertEquals(List.of(), unreadAnywhere(alone), alone);
        String unboundedAlone = report(measured(ALONE_IN_A_LIST.formatted("", "",
                "quote.touches")));
        assertEquals(List.of(), unreadAnywhere(unboundedAlone), unboundedAlone);
        assertFalse(unreadAnywhere(report(measured(ALONE_IN_A_LIST.formatted(bounded, two,
                "quote.touches")))).isEmpty());
        assertFalse(unreadAnywhere(report(measured(ALONE_IN_A_LIST.formatted("", two,
                "quote.touches")))).isEmpty());
        assertFalse(unreadAnywhere(report(measured(ALONE_IN_A_LIST.formatted(bounded, "",
                "List.filter(p -> p.days > 3, quote.touches)")))).isEmpty());
        assertFalse(unreadAnywhere(report(measured(ALONE_IN_A_LIST.formatted("", "",
                "List.filter(p -> p.days > 3, quote.touches)")))).isEmpty());
    }

    private static final String BY_CASE = """
            module example.stale

            data Base = { account: String }
            data Call = { ...Base, a: Int }
                %s
            data Email = { ...Base, b: Int }
                %s
            data Row = Call | Email

            let daysOf (p: Row): Int =
                match p with
                    | Call { a } -> a
                    | Email { b } -> b

            let sinceOf (rows: List<Row>): Map<String, Int> =
                List.fold((acc, p) -> Map.updateOrInsert(p.account, daysOf(p),
                                                         seen -> Int.min(seen, daysOf(p)), acc),
                          Map.empty, rows)

            behavior stale : (rows: List<Row>, staleAfter: Int) -> Map<String, Int>

            let stale (rows, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(rows))
            """;

    /**
     * A number the element's case chooses among places is every value where each case's place is
     * shown the same run, and not where the cases hold different runs: a value of one case's run
     * past the other's is a value only that case's elements take.
     */
    @Test
    void theEndOfANumberChosenByCaseIsShownEveryValueOnlyWhereTheCasesHoldTheSameRun() {
        String alike = report(measured(BY_CASE.formatted("", "")));
        assertEquals(List.of(), unreadAnywhere(alike), alike);
        String apart = report(measured(BY_CASE.formatted("invariant a >= 0", "")));
        assertFalse(unreadAnywhere(apart).isEmpty(), apart);
    }

    private static final String KEPT_BY_WHAT_IT_IS_RELATED_TO = """
            module example.stale

            data ToAccount
            data ToLead
            data Related = ToAccount | ToLead
            data Touch = { account: String, related: Related, days: Int }
                %s

            let onAnAccount (t: Touch): Bool =
                match t.related with
                    | ToAccount -> true
                    | ToLead -> false

            let sinceOf (touches: List<Touch>): Map<String, Int> =
                List.fold((acc, t) -> Map.updateOrInsert(t.account, t.days,
                                                         seen -> Int.min(seen, t.days), acc),
                          Map.empty, List.filter(t -> onAnAccount(t), touches))

            behavior stale : (touches: List<Touch>, staleAfter: Int) -> Map<String, Int>

            let stale (touches, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches))
            """;

    /**
     * An end taken over the touches that are related to an account is shown every value its
     * number takes where one touch alone is a row: that touch is related to an account, and what
     * it is related to is not what the number reads. Where the number is a field of the case that
     * is the relation itself, the touches kept are those with a value, and the proof says so.
     */
    @Test
    void theEndOverASelectionIsShownEveryValueWhereWhatSelectsIsNotWhatTheNumberReads() {
        for (String declared : List.of("", "invariant days >= 0 && days <= 100")) {
            Compilation compilation = measured(KEPT_BY_WHAT_IT_IS_RELATED_TO.formatted(declared));
            String report = report(compilation);
            assertEquals(List.of(), unreadAnywhere(report), report);
            assertTrue(json(compilation).contains("kept by touches meeting"),
                    () -> "the end is taken over the touches kept: " + report);
            assertEquals(List.of(), report.lines().filter(line -> line.contains("no row is at"))
                    .toList(), report);
        }
    }

    private static final Pattern RELATED_TOUCH = Pattern.compile(
            "Touch \\{ account = \"((?:[^\"\\\\]|\\\\.)*)\", related = (ToAccount|ToLead)(?: \\{ \\})?,"
                    + " days = (-?\\d+) \\}");

    /**
     * The rows offered for the end over the touches related to an account are rows: written back
     * with the answer the model gives them, they meet the points on both sides of the line, which
     * a row offered where no touch is kept, or where the kept ones are all above the line, would
     * not.
     */
    @Test
    void theRowsOfferedOverASelectionMeetTheLineWhenWrittenBack() {
        String examples = """

                example stale
                    | "none" : ([], 2) -> []
                """;
        Compilation before = measured(KEPT_BY_WHAT_IT_IS_RELATED_TO.formatted("") + examples);
        List<String> owed = unmetOf(before);
        assertTrue(owed.containsAll(List.of("OFF", "IN")), () -> owed + "\n" + report(before));
        StringBuilder written = new StringBuilder(examples);
        int named = 0;
        for (String input : offeredInputs(before)) {
            Matcher row = Pattern.compile("^\\[(.*)\\], (-?\\d+)$").matcher(input);
            assertTrue(row.matches(), input);
            int staleAfter = Integer.parseInt(row.group(2));
            Map<String, Integer> least = new LinkedHashMap<>();
            Matcher touch = RELATED_TOUCH.matcher(row.group(1));
            int read = 0;
            while (touch.find()) {
                read = touch.end();
                if (touch.group(2).equals("ToAccount")) {
                    least.merge(touch.group(1), Integer.parseInt(touch.group(3)), Math::min);
                }
            }
            assertTrue(row.group(1).isEmpty() || read > 0, input);
            Map<String, Integer> kept = new LinkedHashMap<>();
            least.forEach((account, days) -> {
                if (days >= staleAfter) {
                    kept.put(account, days);
                }
            });
            written.append("    | \"offered ").append(named++).append("\" : (").append(input)
                    .append(") -> ").append(entries(kept)).append("\n");
        }
        Compilation after = measured(KEPT_BY_WHAT_IT_IS_RELATED_TO.formatted("") + written);
        List<String> unmet = unmetOf(after);
        assertFalse(unmet.contains("OFF") || unmet.contains("IN"),
                () -> "the rows offered meet the points: " + unmet + "\n" + written + report(after));
    }

    /**
     * A rule of the touch that reads what it is related to leaves it only some cases, and may
     * leave it none of the cases that keep it: no touch is then kept, and the end is not shown
     * a value because one touch alone would be a row.
     */
    @Test
    void aRuleOfTheTouchNamingWhatKeepsItLeavesTheEndUnshownEveryValue() {
        String report = report(measured(KEPT_BY_WHAT_IT_IS_RELATED_TO.formatted(
                "invariant onlyALead(related)").replace("let onAnAccount", """
                let onlyALead (r: Related): Bool =
                    match r with
                        | ToAccount -> false
                        | ToLead -> true

                let onAnAccount""")));
        assertFalse(unreadAnywhere(report).isEmpty(), report);
    }

    private static final String KEPT_BY_A_NAME_THE_CASES_SHARE = """
            module example.stale

            data ToAccount
            data ToLead
            data Related = ToAccount | ToLead
            data Base = { account: String, related: Related }
            data Call = { ...Base, a: Int }
            data Email = { ...Base, b: Int }
            data Touch = Call | Email

            let onAnAccount (t: Touch): Bool =
                match t.related with
                    | ToAccount -> true
                    | ToLead -> false

            let daysOf (t: Touch): Int =
                match t with
                    | Call { a } -> a
                    | Email { b } -> b

            let sinceOf (touches: List<Touch>): Map<String, Int> =
                List.fold((acc, t) -> Map.updateOrInsert(t.account, daysOf(t),
                                                         seen -> Int.min(seen, daysOf(t)), acc),
                          Map.empty, List.filter(t -> onAnAccount(t), touches))

            behavior stale : (touches: List<Touch>, staleAfter: Int) -> Map<String, Int>

            let stale (touches, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches))
            """;

    /**
     * The case that keeps a touch is read at a name both kinds of touch share, which stands at one
     * position under each kind: the end is shown every value as it is where the name is the
     * touch's own, with the position asked under the kind the number is read in.
     */
    @Test
    void theEndOverASelectionOfANameTheCasesShareIsShownEveryValue() {
        Compilation compilation = measured(KEPT_BY_A_NAME_THE_CASES_SHARE);
        String report = report(compilation);
        assertEquals(List.of(), unreadAnywhere(report), report);
        assertTrue(json(compilation).contains("kept by touches meeting"), report);
        assertEquals(List.of(), report.lines().filter(line -> line.contains("no row is at"))
                .toList(), report);
    }

    /** A rule of the touch about its account does not relate the account to what keeps it. */
    @Test
    void aRuleOfTheTouchAboutAnotherFieldLeavesTheEndShown() {
        String report = report(measured(
                KEPT_BY_WHAT_IT_IS_RELATED_TO.formatted("invariant String.length(account) >= 1")));
        assertEquals(List.of(), unreadAnywhere(report), report);
    }

    /**
     * The premise of showing the end beside the selection: no rule this compiler reads relates the
     * case a touch is in to a number of it. The end is shown every value because the case that
     * keeps the touch and its days are asked of one touch apart ({@code namedDownTo} on the
     * positions the selection reads), and a rule tying them would leave the days of a kept touch
     * only some values. The forms below are the ways to write such a rule, and none is read yet —
     * so the reading that would make one readable is the one to revisit that check beside.
     *
     * <p>The same premise is why no input makes the first way of meeting a statement of several
     * cases build nothing while a later one builds: a way beside what the row asks is refused only
     * by a rule tying the case to something, and so the composer's trying the ways in turn
     * ({@code TermRealizations}) is held by the unit test of the ways and not by a model.
     */
    @Test
    void noRuleRelatingTheCaseOfATouchToItsDaysIsReadYet() {
        for (String tie : List.of(
                "invariant match related with | ToAccount -> days >= 10 | ToLead -> true",
                "invariant days >= 10 || (match related with | ToAccount -> false | ToLead -> true)",
                "invariant if days >= 10 then true else (match related with"
                        + " | ToAccount -> false | ToLead -> true)")) {
            String report = report(measured(KEPT_BY_WHAT_IT_IS_RELATED_TO.formatted(tie)));
            assertTrue(report.contains("invariant Touch #1 — which values may stand at"
                    + " touches[*].related: written in a form this compiler does not read"),
                    () -> "a rule tying the case to the days is read: " + tie + "\n" + report);
        }
    }

    /**
     * A rule leaving the touch none of the cases that keep it keeps no touch: the end is not shown
     * a value because one touch alone would be a row, though the days are tied to nothing.
     */
    @Test
    void aRuleLeavingNoValueAtTheCaseThatKeepsATouchLeavesTheEndUnshown() {
        String report = report(measured(KEPT_BY_WHAT_IT_IS_RELATED_TO.formatted(
                "invariant match related with | ToAccount -> false | ToLead -> true")));
        assertFalse(unreadAnywhere(report).isEmpty(), report);
    }

    private static final String KEPT_BY_THE_CASE_ITSELF = """
            module example.stale

            data Call = { account: String, days: Int }
            data Email = { account: String, days: Int }
            data Touch = Call | Email

            let isACall (t: Touch): Bool =
                match t with
                    | Call -> true
                    | Email -> false

            let daysOf (t: Touch): Int =
                match t with
                    | Call { days } -> days
                    | Email { days } -> days

            let accountOf (t: Touch): String =
                match t with
                    | Call { account } -> account
                    | Email { account } -> account

            let sinceOf (touches: List<Touch>): Map<String, Int> =
                List.fold((acc, t) -> Map.updateOrInsert(accountOf(t), daysOf(t),
                                                         seen -> Int.min(seen, daysOf(t)), acc),
                          Map.empty, List.filter(t -> isACall(t), touches))

            behavior stale : (touches: List<Touch>, staleAfter: Int) -> Map<String, Int>

            let stale (touches, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches))
            """;

    /**
     * Where the touches are kept for the case they are, and the number is read from the case
     * they are in, one touch alone cannot be shown to be both: what keeps it and the number are
     * not apart, and the end is not shown every value.
     */
    @Test
    void theEndOverASelectionOfTheCaseTheNumberIsReadInIsNotShownEveryValue() {
        String report = report(measured(KEPT_BY_THE_CASE_ITSELF));
        assertFalse(unreadAnywhere(report).isEmpty(), report);
    }

    private static final String KEPT_BY_A_FIELD_OF_ONE_CASE = """
            module example.stale

            data ToAccount
            data ToLead
            data Related = ToAccount | ToLead
            data Call = { account: String, related: Related, days: Int }
            data Email = { account: String, related: Related, days: Int }
            data Touch = Call | Email

            let onACallToAnAccount (t: Touch): Bool =
                match t with
                    | Call { related } -> (match related with
                        | ToAccount -> true
                        | ToLead -> false)
                    | Email -> false

            let daysOf (t: Touch): Int =
                match t with
                    | Call { days } -> days
                    | Email { days } -> days

            let accountOf (t: Touch): String =
                match t with
                    | Call { account } -> account
                    | Email { account } -> account

            let sinceOf (touches: List<Touch>): Map<String, Int> =
                List.fold((acc, t) -> Map.updateOrInsert(accountOf(t), daysOf(t),
                                                         seen -> Int.min(seen, daysOf(t)), acc),
                          Map.empty, List.filter(t -> onACallToAnAccount(t), touches))

            behavior stale : (touches: List<Touch>, staleAfter: Int) -> Map<String, Int>

            let stale (touches, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches))
            """;

    /**
     * What keeps a touch is read in one case of it and the number in both: one touch alone is
     * kept only where it is that case, and so is not a row at the other case's number.
     */
    @Test
    void theEndOverASelectionReadInOneCaseIsNotShownEveryValueOfTheOtherCasesNumber() {
        String report = report(measured(KEPT_BY_A_FIELD_OF_ONE_CASE));
        assertFalse(unreadAnywhere(report).isEmpty(), report);
    }

    /** The lines saying a place is not read, of any comparison. */
    private static List<String> unreadAnywhere(String report) {
        return report.lines().filter(line -> line.contains("not read")).toList();
    }

    /** The lines saying the place {@code place} is not read. */
    private static List<String> unreadAbout(String place, String report) {
        return unreadAnywhere(report).stream()
                .filter(line -> line.endsWith("about `" + place + "`")).toList();
    }

    /** Each end of a key a document names. */
    private static List<String> endsOf(Compilation compilation) {
        return Pattern.compile("(?:least|greatest)\\([^\"]*?by account\\)")
                .matcher(json(compilation))
                .results().map(MatchResult::group).distinct().sorted().toList();
    }

    /** The line is written in a document the schema shipped beside this accepts. */
    @Test
    void theDocumentNamingTheEndIsOneTheSchemaAccepts() {
        for (String step : List.of(LEAST, GREATEST)) {
            DocumentShape.assertShapedLikeTheSchema(JSON.readTree(json(measured(
                    modelOf(step, "")))));
        }
    }

    private static String modelWith(String touchRule, String step) {
        return modelOf(step, "").replace("data Touch = { account: String, days: Int }",
                "data Touch = { account: String, days: Int }\n    invariant " + touchRule);
    }

    private static final String WITHIN_A_HUNDRED = "days >= 0 && days <= 100";

    private static final String NOT_SHOWN_TO_REACH = "not shown to reach every value here";

    private static final Pattern AT_A_COMPARISON = Pattern.compile("comparison@(\\S+) ");

    /**
     * The lines saying a place is not read, of every comparison but the one the filter makes of
     * what was filed against {@code staleAfter}.
     *
     * <p>That one is about the end of the key's values and about {@code staleAfter}, whatever the
     * step is, and a run to it may stop on what the step looks up; what is asked here is what the
     * step's own comparison is.
     */
    private static List<String> unreadBeside(String report) {
        Set<String> filtered = report.lines()
                .filter(line -> line.contains("about `staleAfter`")
                        || line.contains("about `least(touches[*].days by account)`"))
                .map(AT_A_COMPARISON::matcher).filter(Matcher::find)
                .map(found -> found.group(0)).collect(Collectors.toSet());
        return report.lines().filter(line -> line.contains("not read")
                && filtered.stream().noneMatch(line::contains)).toList();
    }

    private static final String COMPARED_WITH_WHAT_WAS_FOUND = "Map.updateOrInsert(t.account,"
            + " t.days, seen -> if t.days < seen then t.days else seen, acc)";

    /** A key worked out of the value is no place two elements share, and nothing is said of what
     *  was found under it. */
    private static final String LOOKUP_AND_FILING = """
            match Map.get(t.account, acc) with
                    | None -> Map.insert(t.account, t.days, acc)
                    | Some seen -> Map.insert(t.account,
                          if t.days < seen then t.days else seen, acc)""";

    /**
     * What the step finds under the key is the end of the values of the earlier elements of that
     * key, so the comparison of the element's value against it is read. What was found is the
     * least of the earlier values of the key, which no value above the top of the range can be
     * below: the comparison is false for a value at the top, and may come out either way for every
     * one under it. So it draws one line, at the top, and no value under is divided by it. The same
     * line, and nothing else, however the step is written.
     */
    @Test
    void theComparisonDrawsItsLineAtTheTopOfTheRangeAndNowhereUnderIt() {
        for (String step : List.of(COMPARED_WITH_WHAT_WAS_FOUND, LOOKUP_AND_FILING)) {
            String report = report(read(modelWith(WITHIN_A_HUNDRED, step)));
            assertTrue(report.contains(
                    "no IN point is owed at touches[*].days = 100 (comparison@"), report);
            assertFalse(report.contains("touches[*].days = 0 (comparison@"), report);
            assertEquals(List.of(), unreadBeside(report), report);
        }
    }

    /**
     * Elements of one key hold the number the key is, so what was found is the number of the one
     * compared and no other value: the comparison is false for every value, which the range over
     * every element does not say. Left unread, written either way, under a range that would draw
     * the line at its top for a key apart from the value.
     */
    @Test
    void aKeyThatIsTheValueLeavesTheComparisonUnread() {
        for (String step : List.of(
                "Map.updateOrInsert(t.days, t.days,"
                        + " seen -> if t.days < seen then t.days else seen, acc)",
                """
                match Map.get(t.days, acc) with
                        | None -> Map.insert(t.days, t.days, acc)
                        | Some seen -> Map.insert(t.days,
                              if t.days < seen then t.days else seen, acc)""")) {
            String report = report(read("""
                    module example.stale

                    data Touch = { days: Int }
                        invariant %s

                    let sinceOf (touches: List<Touch>): Map<Int, Int> =
                        List.fold((acc, t) -> %s, Map.empty, touches)

                    behavior stale : (touches: List<Touch>) -> List<Int>

                    let stale (touches) = Map.keys(sinceOf(touches))
                    """.formatted(WITHIN_A_HUNDRED, step)));
            assertTrue(report.contains("not read"), () -> step + "\n" + report);
        }
    }

    /** With at most one element there is no earlier one to have found anything. */
    @Test
    void aListOfOneAtMostHasNoEarlierElementToHaveFoundAValue() {
        String report = report(read("""
                module example.stale

                data Touch = { account: String, days: Int }
                    invariant days >= 0 && days <= 100

                data Quote = { touches: List<Touch> }
                    invariant List.length(touches) <= 1

                let sinceOf (touches: List<Touch>): Map<String, Int> =
                    List.fold((acc, t) -> %s, Map.empty, touches)

                behavior stale : (quote: Quote, staleAfter: Int) -> Map<String, Int>

                let stale (quote, staleAfter) =
                    Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(quote.touches))
                """.formatted(COMPARED_WITH_WHAT_WAS_FOUND)));
        assertTrue(unreadBeside(report).stream()
                .anyMatch(line -> line.contains("it relates the value here to another value "
                        + NOT_SHOWN_TO_REACH)), report);
    }

    @Test
    void theComparisonAfterALookupOfTheKeyIsReadAsTheOneInsideTheClosure() {
        String lookup = """
                match Map.get(t.account, acc) with
                        | None -> Map.insert(t.account, t.days, acc)
                        | Some seen -> Map.insert(t.account,
                              if t.days < seen then t.days else seen, acc)""";
        Compilation compilation = read(modelWith(WITHIN_A_HUNDRED, lookup));
        assertEquals(List.of(), unreadBeside(report(compilation)), () -> report(compilation));
        assertEquals(axisOf(read(modelWith(WITHIN_A_HUNDRED, COMPARED_WITH_WHAT_WAS_FOUND))),
                axisOf(compilation));
    }

    @Test
    void aKeyWorkedOutOfTheValueLeavesTheComparisonUnread() {
        Compilation compilation = read(modelWith(WITHIN_A_HUNDRED,
                "Map.updateOrInsert(String.fromInt(t.days + 1), t.days,"
                        + " seen -> if t.days < seen then t.days else seen, acc)"));
        assertFalse(unreadBeside(report(compilation)).isEmpty(), () -> report(compilation));
    }

    /** A rule of the element relating the key to the value leaves the earlier values of one key
     *  no wider than this one's, which the range over every element does not say. */
    @Test
    void aRuleRelatingTheKeyToTheValueLeavesTheComparisonUnread() {
        Compilation compilation = read(modelWith(
                WITHIN_A_HUNDRED + " && (account /= \"a\" || days <= 10)",
                COMPARED_WITH_WHAT_WAS_FOUND));
        assertFalse(unreadBeside(report(compilation)).isEmpty(), () -> report(compilation));
    }

    /** A rule of the element that reads only the key leaves the numbers of the elements of one key
     *  as free as it leaves every number, so it is no reason to leave the comparison unread. */
    @Test
    void aRuleOfTheElementReadingOnlyTheKeyLeavesTheComparisonRead() {
        for (String step : List.of(COMPARED_WITH_WHAT_WAS_FOUND, LOOKUP_AND_FILING)) {
            String report = report(read(modelWith(
                    WITHIN_A_HUNDRED + " && String.length(account) > 0", step)));
            assertEquals(List.of(), unreadBeside(report), report);
        }
    }

    /** Elements the list's own rule keeps from sharing a key have no earlier element of their key
     *  to be compared with, which the comparison is not read as having. */
    @Test
    void aRuleKeepingTheKeysApartLeavesTheComparisonUnread() {
        Compilation compilation = read("""
                module example.stale

                data Touch = { account: String, days: Int }
                    invariant days >= 0 && days <= 100

                data Quote = { touches: List<Touch> }
                    invariant List.allDistinctBy(t -> t.account, touches)

                let sinceOf (touches: List<Touch>): Map<String, Int> =
                    List.fold((acc, t) -> %s, Map.empty, touches)

                behavior stale : (quote: Quote, staleAfter: Int) -> Map<String, Int>

                let stale (quote, staleAfter) =
                    Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(quote.touches))
                """.formatted(COMPARED_WITH_WHAT_WAS_FOUND));
        assertFalse(unreadBeside(report(compilation)).isEmpty(), () -> report(compilation));
    }

    /** What a fold files that keeps no end of one value of each element says nothing of it. */
    @Test
    void aFoldThatKeepsNoEndOfOneValueIsNotReadAsOne() {
        List<String> steps = List.of(
                // the first element files a value the rest are not compared on
                "Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, t.days + 1), acc)",
                // the rest are compared on another field than the first files
                "Map.updateOrInsert(t.account, t.days, seen -> Int.min(seen, String.length(t.account)), acc)",
                // what the first files turns on what came before
                "Map.updateOrInsert(t.account, Map.size(acc), seen -> Int.min(seen, Map.size(acc)), acc)",
                // under a key that turns on what came before
                "Map.updateOrInsert(String.fromInt(Map.size(acc)), t.days, seen -> Int.min(seen, t.days), acc)",
                // each element replaces what was there
                "Map.insert(t.account, t.days, acc)",
                // another key filed beside the end kept
                "Map.insert(\"other\", 9, " + LEAST + ")");
        for (String step : steps) {
            Compilation compilation = read(modelOf(step, ""));
            assertFalse(json(compilation).contains("least("),
                    () -> "nothing is said of the least of a key's values for " + step + ": "
                            + report(compilation));
        }
    }

    private static String entries(Map<String, Integer> kept) {
        List<String> each = new ArrayList<>();
        kept.forEach((key, value) -> each.add("(\"" + key + "\", " + value + ")"));
        return each.toString();
    }

    /** The points of the lines drawn that no row is at, by name: {@code ON}, {@code OFF},
     *  {@code IN} and {@code OUT}. */
    private static List<String> unmetOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        unmet(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static final Pattern POINT = Pattern.compile("^(ON|OFF|IN|OUT) point of ");

    private static void unmet(JsonNode node, List<String> out) {
        if (node.isObject() && node.has("findings")) {
            node.path("findings").forEach(finding -> {
                Matcher point = POINT.matcher(finding.path("subject").asString());
                if (point.find()) {
                    out.add(point.group(1));
                }
            });
        }
        node.forEach(child -> unmet(child, out));
    }

    /**
     * The elements of a row are read to the end of the list: none from an empty one, a touch
     * whole with an escaped quote in its account, the touch a visit holds, and anything else, or
     * two elements with nothing between them, as a failure rather than an element left out.
     */
    @Test
    void theElementsOfARowAreReadToTheEndOrNotAtAll() {
        assertEquals(List.of(), touchesIn(""));
        assertEquals(List.of(new Touch("a\\\"b", 4), new Touch("c", -1)), touchesIn(
                "Touch { account = \"a\\\"b\", days = 4 }, Visit { touch = Touch { account ="
                        + " \"c\", days = -1 }, note = \"n\" }"));
        for (String unread : List.of("Touch { account = \"a\", days = 4 }, 3",
                "Touch { account = \"a\", days = 4 }Touch { account = \"b\", days = 1 }",
                "Visit { touch = Touch { account = \"c\", days = 1 } }")) {
            assertThrows(AssertionFailedError.class, () -> touchesIn(unread), unread);
        }
    }

    /** A row the block offers, as it is written and as it is read back. */
    private record Offered(String written, Row row) { }

    private static final Pattern ROW = Pattern.compile("^\\[(.*)\\], (-?\\d+)$");

    private static final String TOUCH =
            "Touch \\{ account = \"((?:[^\"\\\\]|\\\\.)*)\", days = (-?\\d+) \\}";

    /** One element of a list of them, where the last one read left off: a touch, or a visit
     *  holding one. */
    private static final Pattern ELEMENT = Pattern.compile("\\G(?:^|, )(?:" + TOUCH
            + "|Visit \\{ touch = " + TOUCH + ", note = \"(?:[^\"\\\\]|\\\\.)*\" \\})");

    /** Every row the block offers, each read back from how it is written — the touch each
     *  element is or holds; a row this cannot read back to its end fails, since a part left
     *  unread is one nothing checks. */
    private static List<Offered> offered(Compilation compilation) {
        List<Offered> out = new ArrayList<>();
        for (String each : offeredInputs(compilation)) {
            Matcher matched = ROW.matcher(each);
            if (!matched.matches()) {
                fail("an offered row is one this reads back: " + each);
            }
            out.add(new Offered(each, new Row(touchesIn(matched.group(1)),
                    Integer.parseInt(matched.group(2)))));
        }
        return out;
    }

    /** The touches {@code list} writes, one element after another to its end, or a failure where
     *  something in it is neither a touch nor a visit holding one. */
    private static List<Touch> touchesIn(String list) {
        List<Touch> touches = new ArrayList<>();
        Matcher one = ELEMENT.matcher(list);
        int read = 0;
        while (one.find()) {
            touches.add(one.group(1) != null
                    ? new Touch(one.group(1), Integer.parseInt(one.group(2)))
                    : new Touch(one.group(3), Integer.parseInt(one.group(4))));
            read = one.end();
        }
        if (read != list.length()) {
            fail("the elements of an offered row are read to the end: " + list + " (read to "
                    + read + ")");
        }
        return touches;
    }

    /** The rows the block offers, read back from how they are written. */
    private static List<Row> offeredRows(Compilation compilation) {
        return offered(compilation).stream().map(Offered::row).toList();
    }

    private static List<String> offeredInputs(Compilation compilation) {
        return Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.stale"))
                .rowsByBehavior().getOrDefault("stale", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    /** Every border drawn, whichever kind of quantity it is on. */
    private static List<JsonNode> bordersOf(Compilation compilation) {
        List<JsonNode> out = new ArrayList<>();
        collect(JSON.readTree(json(compilation)), out);
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out) {
        if (node.isObject() && node.has("items") && node.has("axis")) {
            out.add(node);
        }
        node.forEach(child -> collect(child, out));
    }

    /** The quantity each border is on, as the report names it. */
    private static List<String> axisOf(Compilation compilation) {
        return bordersOf(compilation).stream()
                .map(each -> each.path("axis").asString() + " " + each.path("value").asString())
                .toList();
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Each source measured once for the class at each level: several tests read the same model,
     *  and only read it. */
    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final Map<String, Compilation> READ = new ConcurrentHashMap<>();

    /** And given back when the class is done with them: a fork keeps its JVM, so what is held
     *  statically is held for every class after this one. */
    @AfterAll
    static void released() {
        MEASURED.clear();
        READ.clear();
    }

    /** The source measured, which is a source that compiles. */
    private static Compilation measured(String source) {
        return MEASURED.computeIfAbsent(source,
                text -> compiled(text, Adequacy.Asked.fullReport()));
    }

    /**
     * The source read for the lines its rules draw, and no row composed at them: what a test asks
     * that is about what a comparison is read as, and nothing about a row put on either side of
     * it.
     */
    private static Compilation read(String source) {
        return READ.computeIfAbsent(source,
                text -> compiled(text, Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS)));
    }

    private static Compilation compiled(String source, Adequacy.Asked asked) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(asked);
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + source);
        return compilation;
    }
}
