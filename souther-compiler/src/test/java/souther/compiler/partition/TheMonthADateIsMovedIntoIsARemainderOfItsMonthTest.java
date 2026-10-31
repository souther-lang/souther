package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.time.LocalDate;
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
 * The month a date moved by a number of months written out lands in is what the month of the date
 * less one and the months leave by twelve, plus one: a remainder of the date's month, a line on
 * which rows stand at. A run works out where the move lands and stops past the calendar, which is
 * said where it is. The year and the day the move lands on are not read as anything, and a
 * comparison of the date itself, wherever the move is written, is stopped at the move for what it
 * is: a date no form of the one it moves.
 */
class TheMonthADateIsMovedIntoIsARemainderOfItsMonthTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module demo

            data Yes = { n: Int }
            data No = { n: Int }

            let weekday (c: Date, d: Date): Int = Int.floorMod(Date.daysBetween(c, d), 7)

            behavior f : (c: Date, d: Date) -> Yes | No
            let f (c, d) = {
                %s
                if %s then Yes { n = 1 } else No { n = 0 }
            }
            """;

    /**
     * Each line drawn on what a move lands in is met by rows that run the move: the row at the
     * line lands in the month the comparison names and a row beside it lands in another, read off
     * the dates the rows hold and moved as the runtime moves them. A move of a year and one, or one
     * back, lands in the month of its own remainder.
     */
    @Test
    void theMonthAMoveLandsInIsALineRowsStandAt() {
        for (long months : new long[] {1, 13, -1}) {
            Compilation compilation = measured("", "Date.month(Date.addMonths(" + months
                    + ", d)) == 3");
            List<BorderAssessment> lines = Adequacy.readingsOf(compilation.db(), "demo").get("f");
            assertEquals(1, lines.size(), lines::toString);
            for (Map.Entry<?, ItemAssessment> item : lines.getFirst().items().entrySet()) {
                LocalDate row = certifiedDate(item.getValue());
                boolean atTheLine = item.getKey().toString().startsWith("AtTheLine");
                assertEquals(atTheLine, row.plusMonths(months).getMonthValue() == 3,
                        months + " months from " + row + " at " + item.getKey());
            }
        }
    }

    /** The same move behind a name is the same line. */
    @Test
    void aMoveBehindANameIsTheSameLine() {
        assertEquals(linesOf("", "Date.month(Date.addMonths(1, d)) == 3"),
                linesOf("let e = Date.addMonths(1, d)", "Date.month(e) == 3"));
        assertFalse(linesOf("let e = Date.addMonths(1, d)", "Date.month(e) == 3").isEmpty());
    }

    /** A run stops where the move lands past the calendar, and only there: forward from the
     *  calendar's last month, back from its first. */
    @Test
    void aRunStopsWhereTheMoveLandsPastTheCalendar() {
        assertEquals(List.of("Date.month(d) + 12 * Date.year(d) where Date.month(d) + 12"
                        + " * Date.year(d) 12000000000.."),
                everyRunStops("", "Date.month(Date.addMonths(1, d)) == 3"));
        assertEquals(List.of("Date.month(d) + 12 * Date.year(d) - 2 where Date.month(d) + 12"
                        + " * Date.year(d) ..-11999999987"),
                everyRunStops("", "Date.month(Date.addMonths(-1, d)) == 3"));
        assertEquals(List.of(), everyRunStops("", "Date.month(Date.addMonths(0, d)) == 3"));
    }

    /** The year and the day a move lands on are not read as the month is, nor as anything: no line
     *  is drawn and the date stays unread. */
    @Test
    void theYearAndTheDayAreNotReadAsTheMonthIs() {
        for (String compared : List.of("Date.year(Date.addMonths(1, d)) >= 2027",
                "Date.day(Date.addMonths(1, d)) >= 29")) {
            assertEquals(Set.of(), linesOf("", compared), compared);
            assertTrue(notRead("", compared).contains("d"), compared);
        }
    }

    /**
     * A comparison of the date a move answers is stopped at the move, for being a date no form of
     * the one it moves, wherever the move is written: in the comparison, behind a name, inside a
     * remainder, or in a function it is handed to.
     */
    @Test
    void theDateAMoveAnswersIsStoppedAtTheMoveWhereverItIsWritten() {
        String[][] written = {
                {"", "Date.daysBetween(c, Date.addMonths(1, d)) >= 3"},
                {"let e = Date.addMonths(1, d)", "Date.daysBetween(c, e) >= 3"},
                {"", "Int.floorMod(Date.daysBetween(c, Date.addMonths(1, d)), 7) >= 1"},
                {"let e = Date.addMonths(1, d)", "Int.floorMod(Date.daysBetween(c, e), 7) >= 1"},
                {"", "weekday(c, Date.addMonths(1, d)) >= 1"}};
        for (String[] each : written) {
            String human = human(each[0], each[1]);
            assertTrue(human.contains("what Date.addMonths answers, a date moved by months"),
                    each[1] + "\n" + human);
            assertFalse(human.contains("states no form of"), each[1] + "\n" + human);
            assertEquals(Set.of(at(each[0] + "\n" + each[1], "Date.addMonths")),
                    sentTo(json(each[0], each[1])), each[1]);
        }
    }

    /** The date a certified row of {@code item} holds at {@code d}. */
    private static LocalDate certifiedDate(ItemAssessment item) {
        assertTrue(item instanceof ItemAssessment.Owed, item::toString);
        for (ItemAssessment.Attempt attempt : ((ItemAssessment.Owed) item).searches().each()) {
            if (attempt instanceof ItemAssessment.Attempt.Certified certified) {
                Matcher date = Pattern.compile("Date\\(\"([-0-9]+)\"\\)")
                        .matcher(certified.row().inputs().get(1).text());
                assertTrue(date.matches(), certified.row().inputs()::toString);
                return LocalDate.parse(date.group(1));
            }
        }
        throw new AssertionError("no certified row at " + item);
    }

    /** Each line {@code f} draws, as what it is drawn on and where. */
    private static Set<String> linesOf(String before, String comparison) {
        List<BorderAssessment> lines = Adequacy.readingsOf(measured(before, comparison).db(),
                "demo").get("f");
        Set<String> out = new TreeSet<>();
        if (lines != null) {
            lines.forEach(each -> out.add(each.left() + " " + each.value()));
        }
        return out;
    }

    /** The positions {@code f} leaves unread. */
    private static Set<String> notRead(String before, String comparison) {
        Compilation compilation = measured(before, comparison);
        PartitionEvidence evidence = compilation.db().ask(new Adequacy.Coverage("demo")).value()
                .get("f");
        Set<String> out = new TreeSet<>();
        evidence.notRead().forEach(each -> out.add(each.at().toString()));
        return out;
    }

    /** The rows every run stops at, as {@code operation where form least..greatest}. */
    private static List<String> everyRunStops(String before, String comparison) {
        JsonNode findings = JsonMapper.builder().build().readTree(json(before, comparison))
                .get("modules").get(0).get("behaviors").get(0).get("findings");
        List<String> out = new ArrayList<>();
        for (JsonNode each : findings) {
            if (each.get("kind").asString().equals("rule_may_stop_a_run")
                    && each.has("everyRunStops")) {
                for (JsonNode stop : each.get("everyRunStops")) {
                    List<String> where = new ArrayList<>();
                    for (JsonNode within : stop.get("where")) {
                        where.add(within.get("form").asString() + " "
                                + (within.has("least") ? within.get("least").asString() : "")
                                + ".."
                                + (within.has("greatest") ? within.get("greatest").asString()
                                        : ""));
                    }
                    out.add(stop.get("operation").asString() + " where "
                            + String.join(" and ", where));
                }
            }
        }
        return out;
    }

    /** Where each finding of {@code json} is sent to, as {@code line:column}. */
    private static Set<String> sentTo(String json) {
        Set<String> out = new TreeSet<>();
        Matcher sent = Pattern.compile("\"sentTo\"\\s*:\\s*\\{[^}]*\"line\"\\s*:\\s*(\\d+),"
                + "\\s*\"column\"\\s*:\\s*(\\d+)").matcher(json);
        while (sent.find()) {
            out.add(sent.group(1) + ":" + sent.group(2));
        }
        return out;
    }

    /** Where {@code call} is first written in the body {@code written} is, as
     *  {@code line:column} of the model. */
    private static String at(String written, String call) {
        String model = MODEL.formatted(written.lines().toList().getFirst(),
                written.lines().toList().getLast());
        List<String> lines = model.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            int column = lines.get(i).indexOf(call);
            if (column >= 0 && i > lines.indexOf("let f (c, d) = {")) {
                return (i + 1) + ":" + (column + 1);
            }
        }
        throw new AssertionError(call + " is not written in " + written);
    }

    private static String human(String before, String comparison) {
        Compilation compilation = measured(before, comparison);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String json(String before, String comparison) {
        Compilation compilation = measured(before, comparison);
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** And given back when the class is done with them: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static Compilation measured(String before, String comparison) {
        return MEASURED.computeIfAbsent(MODEL.formatted(before, comparison), source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors(), source);
            return compilation;
        });
    }
}
