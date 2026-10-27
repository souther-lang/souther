package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.Extreme;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.time.LocalDate;
import java.time.LocalDateTime;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * A map a fold files by the day each element's date-time falls on, keeping the least number of
 * days since, holds under a key the days since the latest touch — and a statement about that is a
 * line on the day the latest date-time of the key falls on, the same line a date draws.
 *
 * <p>The end of the days is the day of the end, since a day keeps the order of the seconds in it,
 * and the rows offered at the line are written as the date-times that fall on the days it asks for:
 * written as examples with what the model answers for them, they meet every point of it.
 */
class AFoldOverTheDayADateTimeFallsOnIsReadLikeOneOverADateTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static String model(String touchedAt, String examples) {
        return """
                module example.stale

                data Touch = { account: String, at: %1$s }

                let sinceOf (touches: List<Touch>, today: Date): Map<String, Int> =
                    List.fold((acc, p) -> Map.updateOrInsert(p.account, %2$s,
                                                             seen -> Int.min(seen, %2$s), acc),
                              Map.empty, touches)

                behavior stale : (touches: List<Touch>, today: Date, staleAfter: Int)
                    -> Map<String, Int>

                let stale (touches, today, staleAfter) =
                    Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches, today))
                %3$s""".formatted(touchedAt.equals("Date") ? "Date" : "DateTime",
                touchedAt.equals("Date") ? "Date.daysBetween(p.at, today)"
                        : "Date.daysBetween(DateTime.toDate(p.at), today)", examples);
    }

    private static final String EXAMPLES = """

            example stale
                | "none" : ([], Date("2026-10-23"), 2) -> []
            """;

    /** One row offered for {@code stale}: the touches, today and the threshold. */
    private record Row(List<Touch> touches, LocalDate today, int staleAfter) {

        /** What the model answers for it: the days since the latest touch of each account that
         *  are at least the threshold. */
        Map<String, Long> answer() {
            Map<String, Long> since = new LinkedHashMap<>();
            for (Touch each : touches) {
                long days = ChronoUnit.DAYS.between(each.at().toLocalDate(), today);
                since.merge(each.account(), days, Math::min);
            }
            Map<String, Long> kept = new LinkedHashMap<>();
            since.forEach((account, days) -> {
                if (days >= staleAfter) {
                    kept.put(account, days);
                }
            });
            return kept;
        }

        String written() {
            return "[" + String.join(", ", touches.stream().map(Touch::written).toList())
                    + "], Date(\"" + today + "\"), " + staleAfter;
        }
    }

    private record Touch(String account, LocalDateTime at) {

        String written() {
            return "Touch { account = \"" + account + "\", at = DateTime(\"" + at + "\") }";
        }
    }

    private static final Pattern ROW =
            Pattern.compile("^\\[(.*)\\], Date\\(\"([^\"]+)\"\\), (-?\\d+)$");

    private static final Pattern TOUCH = Pattern.compile("\\G(?:^|, )Touch \\{ account = "
            + "\"((?:[^\"\\\\]|\\\\.)*)\", at = DateTime\\(\"([^\"]+)\"\\) \\}");

    /** The line on the end of the days the latest second of a key falls on is owed all its points,
     *  the rows offered for them are written as the date-times that fall on those days, and
     *  written, they meet them. */
    @Test
    void theRowsOfferedAtTheLineMeetItWhenTheyAreWrittenDown() {
        Compilation before = compiled(model("DateTime", EXAMPLES));
        assertEquals(List.of("ON", "OFF", "IN", "OUT"), unmetOf(before),
                () -> "every point of the line is owed: " + report(before));
        assertTrue(json(before).contains("greatest(DateTime.toDate(touches[*].at) by account)"),
                () -> "the line is on the end of the days: " + report(before));

        List<Row> offered = offered(before);
        assertFalse(offered.isEmpty(), () -> "rows are offered: " + report(before));
        StringBuilder written = new StringBuilder(EXAMPLES);
        int named = 0;
        for (Row row : offered) {
            written.append("    | \"offered ").append(named++).append("\" : (")
                    .append(row.written()).append(") -> ").append(entries(row.answer()))
                    .append("\n");
        }
        Compilation after = compiled(model("DateTime", written.toString()));
        assertEquals(List.of(), unmetOf(after),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /** The rule over a date-time is read as the rule over a date is: every position is a
     *  relation's, and none is a stop. */
    @Test
    void theRuleIsReadAsCompletelyAsTheSameRuleOverADate() {
        for (String touchedAt : List.of("Date", "DateTime")) {
            String report = report(compiled(model(touchedAt, EXAMPLES)));
            assertTrue(report.contains("measurement: complete"), report);
            assertFalse(report.contains("· not read"), report);
        }
    }

    /** A day chosen by the case of each element, one case a date and the other the day a date-time
     *  falls on, is read as completely as the same rule where both cases hold a date. */
    @Test
    void aDayChosenByCaseAmongDatesAndDaysOfDateTimesIsReadLikeOneAmongDates() {
        for (String meetingAt : List.of("Date", "DateTime")) {
            String report = report(compiled("""
                    module example.stale

                    data Call = { on: Date }

                    data Meeting = { at: %1$s }

                    data Act = Call | Meeting

                    data Touch = { account: String, act: Act }

                    let dayOf (a: Act): Date =
                        match a with
                            | Call { on }    -> on
                            | Meeting { at } -> %2$s

                    let sinceOf (touches: List<Touch>, today: Date): Map<String, Int> =
                        List.fold((acc, p) -> Map.updateOrInsert(p.account,
                                      Date.daysBetween(dayOf(p.act), today),
                                      seen -> Int.min(seen, Date.daysBetween(dayOf(p.act), today)),
                                      acc),
                                  Map.empty, touches)

                    behavior stale : (touches: List<Touch>, today: Date, staleAfter: Int)
                        -> Map<String, Int>

                    let stale (touches, today, staleAfter) =
                        Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches, today))
                    """.formatted(meetingAt, meetingAt.equals("Date") ? "at"
                    : "DateTime.toDate(at)")));
            assertTrue(report.contains("measurement: complete"), report);
        }
    }

    private static final ValueName.Stdlib TO_DATE =
            ValueName.Stdlib.operation("DateTime", "toDate");

    /** A fold over touches whose date-time is held to a lower bound, and the end of the days. */
    private static final String A_FOLD_OVER_TOUCHES_AFTER_THE_YEAR_STARTED = """
            module example.stale

            data Touch = { account: String, at: DateTime }
                invariant at >= DateTime("2026-01-01T00:00:00")

            let sinceOf (touches: List<Touch>, today: Date): Map<String, Int> =
                List.fold((acc, p) -> Map.updateOrInsert(p.account,
                              Date.daysBetween(DateTime.toDate(p.at), today),
                              seen -> Int.min(seen, Date.daysBetween(DateTime.toDate(p.at), today)),
                              acc),
                          Map.empty, touches)

            behavior stale : (touches: List<Touch>, today: Date, staleAfter: Int)
                -> Map<String, Int>

            let stale (touches, today, staleAfter) =
                Map.filterEntries((_, days) -> days >= staleAfter, sinceOf(touches, today))
            """;

    private static NumericTerm.ExtremeOfItsKey theLatestDay(InputReading reading) {
        TermPath touches = TermPath.of("touches");
        TermPath at = touches.element().then("at");
        NumericTerm.WholeUnitsOf day = NumericTerm.WholeUnitsOf.of(TO_DATE, at, Type.Prim.DATETIME,
                reading.rules().inners(), reading.rules().declarations());
        assertNotNull(day, "toDate counts the days of the date-times a touch holds");
        return NumericTerm.ExtremeOfItsKey.of(touches, touches.element().then("account"), at,
                Extreme.GREATEST, day);
    }

    private static InputReading readingOf(String source) {
        Compilation read = Compilation.ofSource(source, "Main").writtenOn(TestDay.DATE);
        read.answerEverything();
        RuleReadingSource rules = RuleReadings.of(read, read.modules().get(0));
        return read.db().ask(new Adequacy.Inputs(read.modules().get(0))).value().get("stale")
                .reading(rules);
    }

    /**
     * What the rules leave the end of the days is counted in days, whatever the date-time it is
     * the end of the days of is held to in seconds.
     *
     * <p>The end of some steps is one of those steps and not one of the values they are the steps
     * of. A lower bound on the second a touch is at, carried over unchanged, would be a lower bound
     * of a billion and a half days; carried over by the floor it is the day the year started.
     */
    @Test
    void aBoundOnTheSecondsOfATouchIsABoundOnTheDaysOfTheLatestOne() {
        InputReading reading = readingOf(A_FOLD_OVER_TOUCHES_AFTER_THE_YEAR_STARTED);
        NumericTerm.ExtremeOfItsKey latest = theLatestDay(reading);
        NumericDomain.Bounds days = reading.quantities().runsBetween(latest);

        assertEquals(Count.of(LocalDate.of(2026, 1, 1).toEpochDay()), days.min().at(),
                "the days start where the year does");
        assertEquals(days.min(), reading.quantities().runsBetween(latest.steps()).min(),
                "and the end of the days starts where the days of one touch do");
    }

    /**
     * Whatever is asked of the days, the answer is in days: the steps of one touch and the end of
     * them under a key, over a date-time held to nothing, to a lower bound, and to two values.
     *
     * <p>The class of defect this holds the line against is a reader that answers about a number
     * out of the place it is read from. The days are counted on an order of their own, and every
     * question has to come back on that order — a bound, a projection of the declarations, the
     * values the position's own values read as.
     */
    @Test
    void everyAnswerAboutTheDaysIsInDays() {
        String unconstrained = A_FOLD_OVER_TOUCHES_AFTER_THE_YEAR_STARTED
                .replace("\n    invariant at >= DateTime(\"2026-01-01T00:00:00\")", "");
        String twoValues = A_FOLD_OVER_TOUCHES_AFTER_THE_YEAR_STARTED.replace(
                "invariant at >= DateTime(\"2026-01-01T00:00:00\")",
                "invariant at == DateTime(\"2026-03-15T12:00:00\")"
                        + " || at == DateTime(\"2026-03-16T00:00:00\")");
        assertTrue(!unconstrained.equals(A_FOLD_OVER_TOUCHES_AFTER_THE_YEAR_STARTED)
                && !twoValues.equals(A_FOLD_OVER_TOUCHES_AFTER_THE_YEAR_STARTED));

        for (String source : List.of(unconstrained, A_FOLD_OVER_TOUCHES_AFTER_THE_YEAR_STARTED,
                twoValues)) {
            InputReading reading = readingOf(source);
            NumericTerm.ExtremeOfItsKey latest = theLatestDay(reading);
            NumericDomain.Bounds extent = new NumericDomain.Bounds(
                    reading.quantities().ordersOf(latest).answered().extent().low(),
                    reading.quantities().ordersOf(latest).answered().extent().high());
            for (NumericTerm each : List.of(latest.steps(), latest)) {
                assertTrue(reading.quantities().runsBetween(each).liesWithin(extent),
                        each + " runs within the days: " + source);
                if (reading.quantities().projectionOfTheDeclarations(each)
                        instanceof NumericDomain.FormProjection.Within(var bounds)) {
                    assertTrue(bounds.liesWithin(extent), each + " is held within the days");
                }
            }
        }

        InputReading two = readingOf(twoValues);
        NumericDomain.Bounds days = two.quantities().runsBetween(theLatestDay(two));
        assertEquals(Count.of(LocalDate.of(2026, 3, 15).toEpochDay()), days.min().at());
        assertEquals(Count.of(LocalDate.of(2026, 3, 16).toEpochDay()), days.max().at());
    }

    /** An end is counted on the order of the number it is one of the values of, with the steps and
     *  without them: asked of the one, the other is not answered in another unit. */
    @Test
    void anEndIsCountedOnTheOrderOfTheNumberItIsOneOfTheValuesOf() {
        InputReading reading = readingOf(A_FOLD_OVER_TOUCHES_AFTER_THE_YEAR_STARTED);
        NumericTerm.ExtremeOfItsKey latest = theLatestDay(reading);
        TermPath touches = TermPath.of("touches");
        NumericTerm.ExtremeOfItsKey ofTheSeconds = NumericTerm.ExtremeOfItsKey.of(touches,
                touches.element().then("account"), touches.element().then("at"),
                Extreme.GREATEST);

        for (NumericTerm.ExtremeOfItsKey each : List.of(latest, ofTheSeconds)) {
            assertEquals(reading.quantities().ordersOf(each).answered(),
                    reading.quantities().ordersOf(each.valuesTakenFrom()).answered(),
                    each + " is one of the values of " + each.valuesTakenFrom());
        }
        assertFalse(reading.quantities().ordersOf(latest).answered()
                .equals(reading.quantities().ordersOf(ofTheSeconds).answered()),
                "the days and the seconds are two orders");
    }

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + source);
        return compilation;
    }

    private static List<Row> offered(Compilation compilation) {
        List<Row> out = new ArrayList<>();
        for (String each : Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.stale"))
                .rowsByBehavior().getOrDefault("stale", List.of()).stream()
                .map(row -> String.join(", ",
                        row.inputs().stream().map(FixtureTemplate::text).toList()))
                .toList()) {
            Matcher matched = ROW.matcher(each);
            if (!matched.matches()) {
                fail("an offered row is one this reads back: " + each);
            }
            List<Touch> touches = new ArrayList<>();
            Matcher one = TOUCH.matcher(matched.group(1));
            int read = 0;
            while (one.find()) {
                touches.add(new Touch(one.group(1), LocalDateTime.parse(one.group(2))));
                read = one.end();
            }
            if (read != matched.group(1).length()) {
                fail("the elements of an offered row are read to the end: " + each);
            }
            out.add(new Row(touches, LocalDate.parse(matched.group(2)),
                    Integer.parseInt(matched.group(3))));
        }
        return out;
    }

    private static String entries(Map<String, Long> kept) {
        List<String> each = new ArrayList<>();
        kept.forEach((key, value) -> each.add("(\"" + key + "\", " + value + ")"));
        return each.toString();
    }

    private static final Pattern POINT = Pattern.compile("^(ON|OFF|IN|OUT) point of ");

    private static List<String> unmetOf(Compilation compilation) {
        List<String> out = new ArrayList<>();
        unmet(JSON.readTree(json(compilation)), out);
        return out;
    }

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

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
