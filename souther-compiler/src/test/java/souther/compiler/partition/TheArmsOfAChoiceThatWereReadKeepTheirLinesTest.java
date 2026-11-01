package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.PartitionEvidence;

import java.time.LocalDate;
import java.time.temporal.ChronoUnit;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of a value chosen by cases one of which was not read is a comparison of the others
 * where they are taken: each arm that was read draws its line, deciding where that arm is taken,
 * and the arm that was not read stays a stop of the comparison, with what stopped it. Which order
 * the arms are written in says nothing of which are kept. A line that decides only where the part
 * nothing read comes out some way is none, and inside what a search finds first the lines of each
 * candidate are drawn where the arm read is taken, whatever the arm not read would have found.
 */
class TheArmsOfAChoiceThatWereReadKeepTheirLinesTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String READ_FIRST = """
                    | Net15 -> Date.addDays(15, d)
                    | Net30 -> Date.addDays(30, d)
                    | Eom -> Date.addDays(0 - 1, Date.addMonths(1, d))""";

    private static final String NOT_READ_FIRST = """
                    | Eom -> Date.addDays(0 - 1, Date.addMonths(1, d))
                    | Net15 -> Date.addDays(15, d)
                    | Net30 -> Date.addDays(30, d)""";

    private static final String MODEL = """
            module demo
            data Yes = { n: Int }
            data No = { n: Int }
            data Terms = Net15 | Net30 | Eom
            let due (t: Terms, d: Date): Date =
                match t with
            %s
            let weekday (c: Date, d: Date): Int = Int.floorMod(Date.daysBetween(c, d), 7)
            behavior f : (c: Date, d: Date, t: Terms) -> %s
            let f (c, d, t) = %s
            """;

    /**
     * The two arms read draw a line each, the one where their own arm is taken, in whichever order
     * the arms are written; a row at either line is one taking that arm, whose due day falls on
     * the line's weekday. The arm not read is said, with what stopped it.
     */
    @Test
    void theArmsReadDrawTheirLinesBesideTheOneNotRead() {
        for (String arms : List.of(READ_FIRST, NOT_READ_FIRST)) {
            String model = decides(arms, "weekday(c, due(t, d)) >= 1");
            assertEquals(Set.of("Int.floorMod(-c + d + 1, 7) 1", "Int.floorMod(-c + d + 2, 7) 1"),
                    linesOf(model), arms);
            everyRowAt(model, (line, row) -> {
                String t = row.get(2);
                assertNotEquals("Eom", t, line + " " + row);
                assertEquals(line.contains("+ 1,") ? "Net15" : "Net30", t, line + " " + row);
                LocalDate due = date(row.get(1)).plusDays(t.equals("Net15") ? 15 : 30);
                return weekday(date(row.getFirst()), due) == 1;
            });
            assertTrue(notRead(model).containsAll(Set.of("c", "d", "t")),
                    notRead(model).toString());
        }
    }

    /**
     * A line that decides only where the part nothing read comes out some way is no line: the
     * greater of a weekday and one nothing read is the weekday where that one is below it, which no
     * row can be asked.
     */
    @Test
    void aLineDecidingOnlyBesideWhatWasNotReadIsNone() {
        String model = decides(READ_FIRST,
                "Int.max(weekday(c, d), weekday(c, Date.addMonths(1, d))) >= 3");
        assertEquals(Set.of(), linesOf(model));
        assertTrue(notRead(model).containsAll(Set.of("c", "d")), notRead(model).toString());
    }

    /**
     * Inside what a search finds first among the days from the due day on, each candidate's line
     * is drawn where an arm read is taken: what the arm not read would have found has no say
     * there. A row at a candidate's line takes such an arm, reaches that candidate — every one
     * before it a weekend day — and is on the line's weekday there.
     */
    @Test
    void whatASearchFindsFirstAmongDaysChosenByCasesIsDrawnOnTheArmsRead() {
        String model = MODEL.formatted(READ_FIRST, "Date", """
                List.rangeInclusive(0, 6)
                        |> List.map(n -> Date.addDays(n, due(t, d)))
                        |> List.find(e -> weekday(c, e) >= 1 && weekday(c, e) <= 5)
                        |> Option.withDefault(d)""");
        Pattern on = Pattern.compile("Int\\.floorMod\\(-c \\+ d(?: \\+ (\\d))?, 7\\) (\\d)");
        assertTrue(!linesOf(model).isEmpty(), model);
        everyRowAt(model, (line, row) -> {
            Matcher at = on.matcher(line);
            assertTrue(at.matches(), line);
            int shift = at.group(1) == null ? 0 : Integer.parseInt(at.group(1));
            String t = row.get(2);
            assertNotEquals("Eom", t, line + " " + row);
            LocalDate c = date(row.getFirst());
            LocalDate due = date(row.get(1)).plusDays(t.equals("Net15") ? 15 : 30);
            int from = t.equals("Net15") ? 15 : 30;
            for (int j = 0; j <= 6; j++) {
                if (Math.floorMod(from + j, 7) == shift) {
                    for (int i = 0; i < j; i++) {
                        int before = weekday(c, due.plusDays(i));
                        if (before >= 1 && before <= 5) {
                            return false;
                        }
                    }
                    return weekday(c, due.plusDays(j)) == Integer.parseInt(at.group(2));
                }
            }
            return false;
        });
    }

    private static String decides(String arms, String condition) {
        return MODEL.formatted(arms, "Yes | No",
                "if " + condition + " then Yes { n = 1 } else No { n = 0 }");
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

    /** The positions {@code f} leaves unread. */
    private static Set<String> notRead(String model) {
        PartitionEvidence evidence = measured(model).db().ask(new Adequacy.Coverage("demo"))
                .value().get("f");
        Set<String> out = new TreeSet<>();
        evidence.notRead().forEach(each -> out.add(each.at().toString()));
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

    private static int weekday(LocalDate c, LocalDate d) {
        return (int) Math.floorMod(ChronoUnit.DAYS.between(c, d), 7L);
    }

    private static LocalDate date(String written) {
        Matcher date = Pattern.compile("Date\\(\"([-0-9]+)\"\\)").matcher(written);
        assertTrue(date.matches(), written);
        return LocalDate.parse(date.group(1));
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
