package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a container holds a number made of the input, a date a day after another or one chosen
 * by cases, is what a comparison of that number with the elements written with {@code ==} states:
 * a relation of the elements to the numbers it is made of, a line rows stand at. Read so, a
 * membership a statement holds beside other lines is a condition a row is asked to meet, and the
 * lines of what a search finds first are drawn where it holds.
 */
class AMembershipOfANumberIsTheRelationAComparisonOfItStatesTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String CALENDAR = """
            data Cal = { aSunday: Date, holidays: Set<Date> }
            let weekday (cal: Cal, d: Date): Int = Int.floorMod(Date.daysBetween(cal.aSunday, d), 7)
            let open (cal: Cal, d: Date): Bool = weekday(cal, d) >= 1 && weekday(cal, d) <= 5%s
            """;

    private static final String HOLDS = """
            module demo
            data Yes = { n: Int }
            data No = { n: Int }
            %s
            data Terms = Net15 | Net30
            let nominal (t: Terms, d: Date): Date =
                match t with
                    | Net15 -> Date.addDays(15, d)
                    | Net30 -> Date.addDays(30, d)
            behavior f : (cal: Cal, hs: List<Date>, d: Date, t: Terms) -> Yes | No
            let f (cal, hs, d, t) = {
                %s
                if %s then Yes { n = 1 } else No { n = 0 }
            }
            """;

    private static final String FINDS = """
            module demo
            %s
            behavior f : (cal: Cal, d: Date) -> Date
            let f (cal, d) =
                List.rangeInclusive(0, 6)
                    |> List.map(n -> Date.addDays(n, d))
                    |> List.find(e -> open(cal, e))
                    |> Option.withDefault(d)
            """;

    private static final String NOT_A_HOLIDAY = "\n    && Bool.not(Set.contains(d, cal.holidays))";

    /**
     * A container holding the day after a date draws the line a comparison of its elements with
     * that day draws — the one relation, faced as a law faces it, with no side written first — and
     * a row at the line is one whose container holds the day: the rows are read back and the
     * membership worked out of what they hold.
     */
    @Test
    void holdingTheDayAfterADateIsTheLineAComparisonWithItDraws() {
        String held = "List.contains(Date.addDays(1, d), hs)";
        assertEquals(Set.of("hs[*] d + 1"),
                linesOf(holds("List.any(h -> h == Date.addDays(1, d), hs)")));
        assertEquals(Set.of("d hs[*] - 1"), linesOf(holds(held)));
        assertEquals(Set.of("d cal.holidays[*] - 1"),
                linesOf(holds("Set.contains(Date.addDays(1, d), cal.holidays)")));
        everyRowAt(holds(held), (line, row) -> {
            LocalDate d = date(row.get(2));
            return dates(row.get(1)).contains(d.plusDays(1));
        });
    }

    /** The day behind a name is the day written out: the same line, and rows at it hold the day. */
    @Test
    void theDayBehindANameIsTheDayWrittenOut() {
        String named = holds("let e = Date.addDays(1, d)", "List.contains(e, hs)");
        assertEquals(linesOf(holds("List.contains(Date.addDays(1, d), hs)")), linesOf(named));
        everyRowAt(named, (line, row) ->
                dates(row.get(1)).contains(date(row.get(2)).plusDays(1)));
    }

    /** A value chosen by cases is held on each of them, as a comparison of it is read. */
    @Test
    void aValueChosenByCasesIsHeldOnEachOfThem() {
        String held = "List.contains(nominal(t, d), hs)";
        assertEquals(Set.of("hs[*] d + 15", "hs[*] d + 30"),
                linesOf(holds("List.any(h -> h == nominal(t, d), hs)")));
        assertEquals(Set.of("d hs[*] - 15", "d hs[*] - 30"), linesOf(holds(held)));
        everyRowAt(holds(held), (line, row) -> {
            LocalDate d = date(row.get(2));
            LocalDate nominal = d.plusDays(row.get(3).equals("Net15") ? 15 : 30);
            return dates(row.get(1)).contains(nominal);
        });
    }

    /**
     * What a search finds first is drawn where the day it is at is open, with or without holidays
     * beside the weekday: the same lines, each of them on the candidate a run reaches. A row at the
     * line on a candidate is one that reaches it — every candidate before it closed, by the weekday
     * or by a holiday the row's calendar holds — and whose weekday there is the line's.
     */
    @Test
    void theLinesOfWhatASearchFindsFirstAreDrawnBesideAHoliday() {
        String withHolidays = FINDS.formatted(CALENDAR.formatted(NOT_A_HOLIDAY));
        assertEquals(linesOf(FINDS.formatted(CALENDAR.formatted(""))), linesOf(withHolidays));
        Pattern candidate = Pattern.compile(
                "Int\\.floorMod\\(-cal\\.aSunday \\+ d(?: \\+ (\\d))?, 7\\) (\\d)");
        List<String> reachedPastAClosedDay = new ArrayList<>();
        everyRowAt(withHolidays, (line, row) -> {
            Matcher on = candidate.matcher(line);
            assertTrue(on.matches(), line);
            int j = on.group(1) == null ? 0 : Integer.parseInt(on.group(1));
            LocalDate sunday = date(field(row.getFirst(), "aSunday"));
            Set<LocalDate> holidays = dates(field(row.getFirst(), "holidays"));
            LocalDate d = date(row.get(1));
            for (int i = 0; i < j; i++) {
                if (open(sunday, holidays, d.plusDays(i))) {
                    return false;
                }
            }
            if (j > 0) {
                reachedPastAClosedDay.add(line);
            }
            return weekday(sunday, d.plusDays(j)) == Integer.parseInt(on.group(2));
        });
        assertFalse(reachedPastAClosedDay.isEmpty());
    }

    /** Each line of {@code model}'s {@code f}, as what it is drawn on and where. */
    private static Set<String> linesOf(String model) {
        List<BorderAssessment> lines = Adequacy.readingsOf(measured(model).db(), "demo").get("f");
        Set<String> out = new TreeSet<>();
        if (lines != null) {
            lines.forEach(each -> out.add(each.left() + " " + each.value()));
        }
        return out;
    }

    /** What a certified row at a line holds, asked of every one there is. */
    private interface AtTheLine {
        boolean holds(String line, List<String> row);
    }

    /** {@code atTheLine} of every row certified at a line of {@code model}, and its denial of
     *  every row certified beside one; and some row is certified at a line. */
    private static void everyRowAt(String model, AtTheLine atTheLine) {
        boolean some = false;
        for (BorderAssessment border : Adequacy.readingsOf(measured(model).db(), "demo")
                .get("f")) {
            String line = border.left() + " " + border.value();
            for (Map.Entry<?, ItemAssessment> item : border.items().entrySet()) {
                List<String> row = certified(item.getValue());
                if (row == null) {
                    continue;
                }
                boolean at = item.getKey().toString().startsWith("AtTheLine");
                some |= at;
                if (at || item.getKey().toString().startsWith("BesideTheLine")) {
                    assertEquals(at, atTheLine.holds(line, row), line + " " + item.getKey()
                            + " " + row);
                }
            }
        }
        assertTrue(some, model);
    }

    /** The inputs of the row certified for {@code item}, as written, or null where none is. */
    private static List<String> certified(ItemAssessment item) {
        if (!(item instanceof ItemAssessment.Owed owed)) {
            return null;
        }
        for (ItemAssessment.Attempt attempt : owed.searches().each()) {
            if (attempt instanceof ItemAssessment.Attempt.Certified row) {
                return row.row().inputs().stream().map(each -> each.text()).toList();
            }
        }
        return null;
    }

    private static boolean open(LocalDate sunday, Set<LocalDate> holidays, LocalDate d) {
        int weekday = weekday(sunday, d);
        return weekday >= 1 && weekday <= 5 && !holidays.contains(d);
    }

    private static int weekday(LocalDate sunday, LocalDate d) {
        return (int) Math.floorMod(ChronoUnit.DAYS.between(sunday, d), 7L);
    }

    /** What {@code record} writes at {@code name}. */
    private static String field(String record, String name) {
        Matcher at = Pattern.compile(name + " = (\\[[^]]*]|Date\\(\"[-0-9]+\"\\))").matcher(record);
        assertTrue(at.find(), record);
        return at.group(1);
    }

    private static LocalDate date(String written) {
        Matcher date = Pattern.compile("Date\\(\"([-0-9]+)\"\\)").matcher(written);
        assertTrue(date.matches(), written);
        return LocalDate.parse(date.group(1));
    }

    private static Set<LocalDate> dates(String written) {
        Set<LocalDate> out = new TreeSet<>();
        Matcher date = Pattern.compile("Date\\(\"([-0-9]+)\"\\)").matcher(written);
        while (date.find()) {
            out.add(LocalDate.parse(date.group(1)));
        }
        return out;
    }

    private static String holds(String held) {
        return holds("", held);
    }

    private static String holds(String before, String held) {
        return HOLDS.formatted(CALENDAR.formatted(""), before, held);
    }

    /** And given back when the class is done with them: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static Compilation measured(String model) {
        return MEASURED.computeIfAbsent(model, source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors(), source);
            return compilation;
        });
    }
}
