package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

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
 * A container asked for a member the source wrote is asked of its elements what a comparison of
 * them with that value is: the line is at the value, a row at it holds the value, and a row on
 * either side holds an element below it or above it. A member that is another place of the row
 * is a relation of two values and draws none.
 */
class AContainerAskedForAWrittenMemberDrawsTheLineAComparisonWithItDrawsTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module probe
            data Group = { tags: List<String> }
            data Line = { code: String, rates: Map<String, Int>, tags: List<String>,
                          ids: Set<String>, nums: List<Int>, days: List<Date>, n: Int,
                          other: List<String>, groups: List<Group> }

            behavior any : (l: Line) -> Bool
            let any (l) = List.any(t -> t == "K", l.tags)
            behavior listed : (l: Line) -> Bool
            let listed (l) = List.contains("K", l.tags)
            behavior setted : (l: Line) -> Bool
            let setted (l) = Set.contains("K", l.ids)
            behavior keyed : (l: Line) -> Bool
            let keyed (l) = Map.containsKey("USD", l.rates)
            behavior absent : (l: Line) -> Bool
            let absent (l) = Bool.not(List.contains("K", l.tags))
            behavior numbered : (l: Line) -> Bool
            let numbered (l) = List.contains(5, l.nums)
            behavior anyDay : (l: Line) -> Bool
            let anyDay (l) = List.any(d -> d == Date("2026-01-05"), l.days)
            behavior hasDay : (l: Line) -> Bool
            let hasDay (l) = List.contains(Date("2026-01-05"), l.days)
            behavior another : (l: Line) -> Bool
            let another (l) = Map.containsKey(l.code, l.rates)

            behavior guarded : (l: Line) -> Int
            let guarded (l) = if Map.containsKey("USD", l.rates) then 1 else 0
            behavior alongside : (l: Line) -> Int
            let alongside (l) = if List.contains("K", l.tags) && l.n > 3 then 1 else 0
            behavior alongsideAny : (l: Line) -> Int
            let alongsideAny (l) = if List.any(t -> t == "K", l.tags) && l.n > 3 then 1 else 0
            behavior either : (l: Line) -> Int
            let either (l) = if List.contains("K", l.tags) || List.contains("M", l.other) then 1 else 0
            behavior eitherAny : (l: Line) -> Int
            let eitherAny (l) = if List.any(t -> t == "K", l.tags) || List.any(t -> t == "M", l.other) then 1 else 0
            behavior inEachGroup : (l: Line) -> Bool
            let inEachGroup (l) = List.all(g -> List.contains("K", g.tags), l.groups)
            behavior inEachGroupAny : (l: Line) -> Bool
            let inEachGroupAny (l) = List.all(g -> List.any(t -> t == "K", g.tags), l.groups)
            behavior comparedTrue : (l: Line) -> Int
            let comparedTrue (l) = if List.contains("K", l.tags) == true then 1 else 0
            behavior twoElements : (l: Line) -> Bool
            let twoElements (l) = List.contains("K", l.tags) && List.contains("L", l.tags)

            data Tagged = { tags: List<String> } invariant List.contains("K", tags)
            behavior heldBesideK : (t: Tagged) -> Bool
            let heldBesideK (t) = List.contains("L", t.tags)
            """;

    /** What a comparison of the elements draws is what holding the value in a list, a set or a
     *  map's keys draws, however the statement is written. */
    @Test
    void holdingTheValueDrawsTheLineComparingTheElementsWithItDraws() {
        assertEquals(Set.of("l.tags[*] K"), linesOf("any"));
        assertEquals(linesOf("any"), linesOf("listed"));
        assertEquals(linesOf("any"), linesOf("absent"));
        assertEquals(Set.of("l.ids[*] K"), linesOf("setted"));
        assertEquals(Set.of("l.rates[key] USD"), linesOf("keyed"));
        assertEquals(linesOf("keyed"), linesOf("guarded"));
        assertEquals(Set.of("l.nums[*] 5"), linesOf("numbered"));
        assertEquals(Set.of("l.days[*] 2026-01-05"), linesOf("anyDay"));
        assertEquals(linesOf("anyDay"), linesOf("hasDay"));
    }

    /** Written beside other statements, under a closure or twice over one container, the lines
     *  are those the comparison written with {@code any} draws, each with its rows. */
    @Test
    void theLinesAreTheSameWhereTheStatementIsPartOfAnother() {
        for (String[] pair : new String[][] {
            { "alongside", "alongsideAny" }, { "either", "eitherAny" },
            { "inEachGroup", "inEachGroupAny" } }) {
            assertEquals(linesOf(pair[1]), linesOf(pair[0]), pair[0]);
            assertEquals(certifiedPointsOf(pair[1]), certifiedPointsOf(pair[0]), pair[0]);
        }
        assertEquals(Set.of("l.n 3", "l.tags[*] K"), linesOf("alongside"));
        assertEquals(Set.of("l.tags[*] K", "l.other[*] M"), linesOf("either"));
        assertEquals(Set.of("l.groups[*].tags[*] K"), linesOf("inEachGroup"));
        assertEquals(Set.of("l.tags[*] K", "l.tags[*] L"), linesOf("twoElements"));
    }

    /** Every point of every line is searched, and the row found holds what the point says of the
     *  elements: the value at the line, an element below it or above it beside it. */
    @Test
    void everyPointHasARowThatHoldsWhatItSaysOfTheElements() {
        pointsHold("listed", "tags", Kind.TEXT, "K");
        pointsHold("setted", "ids", Kind.TEXT, "K");
        pointsHold("keyed", "rates", Kind.KEY, "USD");
        pointsHold("absent", "tags", Kind.TEXT, "K");
        pointsHold("guarded", "rates", Kind.KEY, "USD");
        pointsHold("numbered", "nums", Kind.NUMBER, "5");
        pointsHold("hasDay", "days", Kind.DAY, "2026-01-05");
    }

    /** The two sides of the line are owed where the neighbour of the value exists: a number and
     *  a date have one a step either side, a string has none. */
    @Test
    void aNumberAndADateHaveTheirNeighboursAndAStringHasNone() {
        assertEquals(Set.of("AtTheLine", "BesideTheLine[side=BELOW]",
                "BesideTheLine[side=ABOVE]", "InTheRegion[side=BELOW]",
                "InTheRegion[side=ABOVE]"), certifiedPointsOf("numbered"));
        assertEquals(certifiedPointsOf("numbered"), certifiedPointsOf("hasDay"));
        assertEquals(Set.of("AtTheLine", "InTheRegion[side=BELOW]", "InTheRegion[side=ABOVE]"),
                certifiedPointsOf("listed"));
    }

    /** A container that must hold another value is still asked for the one the line is at: a
     *  row at it holds both, and a row beside it holds one below or above and the one it must. */
    @Test
    void aContainerThatMustHoldAnotherValueIsStillAskedForTheLine() {
        assertEquals(Set.of("t.tags[*] L"), linesOf("heldBesideK"));
        pointsHold("heldBesideK", "tags", Kind.TEXT, "L");
        for (BorderAssessment border : borders("heldBesideK")) {
            for (ItemAssessment item : border.items().values()) {
                String row = certified(item);
                if (row != null) {
                    assertTrue(elements(row, "tags", Kind.TEXT).contains("K"), row);
                }
            }
        }
    }

    /** The statement is one reading and not two: a comparison of it with {@code true} does not
     *  also say it relates the value to another value. */
    @Test
    void theReportDoesNotSayItRelatesTheValueToAnotherWhereItDrawsALine() {
        String report = AdequacyReport.of(measured()).humanInEnglish(
                SourceRendering.namedByIdentity(SourceLayouts.NONE));
        for (String line : report.split("\n")) {
            assertFalse(line.contains("relates the value here to another value")
                    && line.contains("l.tags[*]"), line);
        }
        assertEquals(linesOf("comparedTrue"), Set.of("l.tags[*] K"));
    }

    /** The member being another place of the row relates two values and divides neither. */
    @Test
    void aMemberThatIsAnotherPlaceDrawsNoLine() {
        assertEquals(Set.of(), linesOf("another"));
    }

    private enum Kind { TEXT, KEY, NUMBER, DAY }

    /** Each certified row of {@code behavior}'s line holds, in {@code field}, what its point says
     *  against {@code at}. */
    private static void pointsHold(String behavior, String field, Kind kind, String at) {
        int checked = 0;
        for (BorderAssessment border : borders(behavior)) {
            for (Map.Entry<?, ItemAssessment> item : border.items().entrySet()) {
                String row = certified(item.getValue());
                if (row == null) {
                    continue;
                }
                String point = item.getKey().toString();
                List<String> held = elements(row, field, kind);
                boolean equal = held.stream().anyMatch(each -> compare(each, at, kind) == 0);
                boolean below = held.stream().anyMatch(each -> compare(each, at, kind) < 0);
                boolean above = held.stream().anyMatch(each -> compare(each, at, kind) > 0);
                if (point.startsWith("AtTheLine")) {
                    assertTrue(equal, behavior + " " + point + " " + row);
                } else if (point.endsWith("side=BELOW]")) {
                    assertTrue(below, behavior + " " + point + " " + row);
                } else {
                    assertTrue(above, behavior + " " + point + " " + row);
                }
                checked++;
            }
        }
        assertTrue(checked >= 3, behavior + " " + checked);
    }

    private static int compare(String element, String at, Kind kind) {
        return kind == Kind.NUMBER
                ? Long.compare(Long.parseLong(element), Long.parseLong(at))
                : element.compareTo(at);
    }

    /** The elements {@code field} holds in {@code row}, as the text of each: the strings, the
     *  keys of a map, the numbers or the days. */
    private static List<String> elements(String row, String field, Kind kind) {
        Matcher held = Pattern.compile(field + " = \\[(.*?)\\](?:, \\w+ =| \\})").matcher(row);
        assertTrue(held.find(), row);
        String inside = held.group(1);
        Pattern each = switch (kind) {
            case TEXT -> Pattern.compile("\"([^\"]*)\"");
            case KEY -> Pattern.compile("\\(\"([^\"]*)\", ");
            case NUMBER -> Pattern.compile("(-?\\d+)");
            case DAY -> Pattern.compile("Date\\(\"([-0-9]+)\"\\)");
        };
        List<String> out = new ArrayList<>();
        Matcher found = each.matcher(inside);
        while (found.find()) {
            out.add(found.group(1));
        }
        return out;
    }

    private static Set<String> linesOf(String behavior) {
        Set<String> out = new TreeSet<>();
        borders(behavior).forEach(each -> out.add(each.left() + " " + each.value()));
        return out;
    }

    /** Which points of {@code behavior}'s lines a row was found for, by the name of the point. */
    private static Set<String> certifiedPointsOf(String behavior) {
        Set<String> out = new TreeSet<>();
        for (BorderAssessment border : borders(behavior)) {
            for (Map.Entry<?, ItemAssessment> item : border.items().entrySet()) {
                if (certified(item.getValue()) != null) {
                    out.add(item.getKey().toString().replace("[]", ""));
                }
            }
        }
        return out;
    }

    private static List<BorderAssessment> borders(String behavior) {
        List<BorderAssessment> lines = Adequacy.readingsOf(measured().db(), "probe").get(behavior);
        return lines == null ? List.of() : lines;
    }

    private static String certified(ItemAssessment item) {
        if (!(item instanceof ItemAssessment.Owed owed)) {
            return null;
        }
        for (ItemAssessment.Attempt attempt : owed.searches().each()) {
            if (attempt instanceof ItemAssessment.Attempt.Certified row) {
                return row.row().inputs().stream().map(each -> each.text()).toList().toString();
            }
        }
        return null;
    }

    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static Compilation measured() {
        return MEASURED.computeIfAbsent(MODEL, source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors(), source);
            return compilation;
        });
    }
}
